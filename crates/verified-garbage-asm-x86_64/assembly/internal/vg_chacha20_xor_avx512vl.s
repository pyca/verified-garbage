// The functions of `src/internal/vg_chacha20_xor_avx512vl.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor_avx512vl:
	cmp rdx, 385
	jb 20f
	call {vg_chacha20_xor_avx512}
	jmp 21f
20:
	movabs rax, 0
	mov QWORD PTR [rcx+224], rax
	movabs rax, 0
	mov QWORD PTR [rcx+232], rax
	movabs rax, 1
	mov QWORD PTR [rcx+240], rax
	movabs rax, 0
	mov QWORD PTR [rcx+248], rax
	movabs rax, 2
	mov QWORD PTR [rcx+256], rax
	movabs rax, 0
	mov QWORD PTR [rcx+264], rax
	movabs rax, 3
	mov QWORD PTR [rcx+272], rax
	movabs rax, 0
	mov QWORD PTR [rcx+280], rax
	movabs rax, 361421592464458498
	mov QWORD PTR [rcx+128], rax
	movabs rax, 940142975169071882
	mov QWORD PTR [rcx+136], rax
	movabs rax, 361421592464458498
	mov QWORD PTR [rcx+144], rax
	movabs rax, 940142975169071882
	mov QWORD PTR [rcx+152], rax
	movabs rax, 433757367256023043
	mov QWORD PTR [rcx+160], rax
	movabs rax, 1012478749960636427
	mov QWORD PTR [rcx+168], rax
	movabs rax, 433757367256023043
	mov QWORD PTR [rcx+176], rax
	movabs rax, 1012478749960636427
	mov QWORD PTR [rcx+184], rax
	movabs rax, 4294967296
	mov QWORD PTR [rcx+192], rax
	movabs rax, 12884901890
	mov QWORD PTR [rcx+200], rax
	movabs rax, 21474836484
	mov QWORD PTR [rcx+208], rax
	movabs rax, 30064771078
	mov QWORD PTR [rcx+216], rax
	mov r11, r8
	sub r11, rsi
	cmp rdx, 512
	jb 22f
24:
	vbroadcasti128 ymm12, XMMWORD PTR [rdi]
	vpshufd ymm0, ymm12, 0
	vpshufd ymm1, ymm12, 85
	vpshufd ymm2, ymm12, 170
	vpshufd ymm3, ymm12, 255
	vbroadcasti128 ymm12, XMMWORD PTR [rdi+16]
	vpshufd ymm4, ymm12, 0
	vpshufd ymm5, ymm12, 85
	vpshufd ymm6, ymm12, 170
	vpshufd ymm7, ymm12, 255
	vbroadcasti128 ymm12, XMMWORD PTR [rdi+48]
	vpshufd ymm8, ymm12, 0
	vpshufd ymm9, ymm12, 85
	vpshufd ymm10, ymm12, 170
	vpshufd ymm11, ymm12, 255
	vmovdqu ymm13, YMMWORD PTR [rcx+192]
	vpaddd ymm8, ymm8, ymm13
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+32]
	vpshufd ymm12, ymm14, 0
	vpshufd ymm13, ymm14, 85
	vpshufd ymm15, ymm14, 170
	vmovdqu YMMWORD PTR [rcx+64], ymm15
	vpshufd ymm15, ymm14, 255
	vmovdqu YMMWORD PTR [rcx+96], ymm15
	vmovdqu ymm15, YMMWORD PTR [rcx+128]
	vmovdqu ymm14, YMMWORD PTR [rcx+64]
	vmovdqu ymm15, YMMWORD PTR [rcx+96]
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vmovdqu YMMWORD PTR [rcx+64], ymm14
	vmovdqu YMMWORD PTR [rcx+96], ymm15
	vmovdqu ymm15, YMMWORD PTR [rcx+128]
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vpunpckldq ymm12, ymm0, ymm1
	vpunpckhdq ymm13, ymm0, ymm1
	vpunpckldq ymm14, ymm2, ymm3
	vpunpckhdq ymm15, ymm2, ymm3
	vpunpcklqdq ymm0, ymm12, ymm14
	vpunpckhqdq ymm1, ymm12, ymm14
	vpunpcklqdq ymm2, ymm13, ymm15
	vpunpckhqdq ymm3, ymm13, ymm15
	vbroadcasti128 ymm14, XMMWORD PTR [rdi]
	vpaddd ymm0, ymm0, ymm14
	vpaddd ymm1, ymm1, ymm14
	vpaddd ymm2, ymm2, ymm14
	vpaddd ymm3, ymm3, ymm14
	vpxor xmm12, xmm0, XMMWORD PTR [rsi]
	vmovdqu XMMWORD PTR [rsi+r11*1], xmm12
	vextracti128 xmm13, ymm0, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+256]
	vmovdqu XMMWORD PTR [rsi+r11*1+256], xmm12
	vpxor xmm12, xmm1, XMMWORD PTR [rsi+64]
	vmovdqu XMMWORD PTR [rsi+r11*1+64], xmm12
	vextracti128 xmm13, ymm1, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+320]
	vmovdqu XMMWORD PTR [rsi+r11*1+320], xmm12
	vpxor xmm12, xmm2, XMMWORD PTR [rsi+128]
	vmovdqu XMMWORD PTR [rsi+r11*1+128], xmm12
	vextracti128 xmm13, ymm2, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+384]
	vmovdqu XMMWORD PTR [rsi+r11*1+384], xmm12
	vpxor xmm12, xmm3, XMMWORD PTR [rsi+192]
	vmovdqu XMMWORD PTR [rsi+r11*1+192], xmm12
	vextracti128 xmm13, ymm3, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+448]
	vmovdqu XMMWORD PTR [rsi+r11*1+448], xmm12
	vpunpckldq ymm12, ymm4, ymm5
	vpunpckhdq ymm13, ymm4, ymm5
	vpunpckldq ymm14, ymm6, ymm7
	vpunpckhdq ymm15, ymm6, ymm7
	vpunpcklqdq ymm4, ymm12, ymm14
	vpunpckhqdq ymm5, ymm12, ymm14
	vpunpcklqdq ymm6, ymm13, ymm15
	vpunpckhqdq ymm7, ymm13, ymm15
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+16]
	vpaddd ymm4, ymm4, ymm14
	vpaddd ymm5, ymm5, ymm14
	vpaddd ymm6, ymm6, ymm14
	vpaddd ymm7, ymm7, ymm14
	vpxor xmm12, xmm4, XMMWORD PTR [rsi+16]
	vmovdqu XMMWORD PTR [rsi+r11*1+16], xmm12
	vextracti128 xmm13, ymm4, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+272]
	vmovdqu XMMWORD PTR [rsi+r11*1+272], xmm12
	vpxor xmm12, xmm5, XMMWORD PTR [rsi+80]
	vmovdqu XMMWORD PTR [rsi+r11*1+80], xmm12
	vextracti128 xmm13, ymm5, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+336]
	vmovdqu XMMWORD PTR [rsi+r11*1+336], xmm12
	vpxor xmm12, xmm6, XMMWORD PTR [rsi+144]
	vmovdqu XMMWORD PTR [rsi+r11*1+144], xmm12
	vextracti128 xmm13, ymm6, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+400]
	vmovdqu XMMWORD PTR [rsi+r11*1+400], xmm12
	vpxor xmm12, xmm7, XMMWORD PTR [rsi+208]
	vmovdqu XMMWORD PTR [rsi+r11*1+208], xmm12
	vextracti128 xmm13, ymm7, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+464]
	vmovdqu XMMWORD PTR [rsi+r11*1+464], xmm12
	vmovdqu ymm15, YMMWORD PTR [rcx+192]
	vpaddd ymm8, ymm8, ymm15
	vpunpckldq ymm12, ymm8, ymm9
	vpunpckhdq ymm13, ymm8, ymm9
	vpunpckldq ymm14, ymm10, ymm11
	vpunpckhdq ymm15, ymm10, ymm11
	vpunpcklqdq ymm8, ymm12, ymm14
	vpunpckhqdq ymm9, ymm12, ymm14
	vpunpcklqdq ymm10, ymm13, ymm15
	vpunpckhqdq ymm11, ymm13, ymm15
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+48]
	vpaddd ymm8, ymm8, ymm14
	vpaddd ymm9, ymm9, ymm14
	vpaddd ymm10, ymm10, ymm14
	vpaddd ymm11, ymm11, ymm14
	vpxor xmm12, xmm8, XMMWORD PTR [rsi+48]
	vmovdqu XMMWORD PTR [rsi+r11*1+48], xmm12
	vextracti128 xmm13, ymm8, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+304]
	vmovdqu XMMWORD PTR [rsi+r11*1+304], xmm12
	vpxor xmm12, xmm9, XMMWORD PTR [rsi+112]
	vmovdqu XMMWORD PTR [rsi+r11*1+112], xmm12
	vextracti128 xmm13, ymm9, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+368]
	vmovdqu XMMWORD PTR [rsi+r11*1+368], xmm12
	vpxor xmm12, xmm10, XMMWORD PTR [rsi+176]
	vmovdqu XMMWORD PTR [rsi+r11*1+176], xmm12
	vextracti128 xmm13, ymm10, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+432]
	vmovdqu XMMWORD PTR [rsi+r11*1+432], xmm12
	vpxor xmm12, xmm11, XMMWORD PTR [rsi+240]
	vmovdqu XMMWORD PTR [rsi+r11*1+240], xmm12
	vextracti128 xmm13, ymm11, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+496]
	vmovdqu XMMWORD PTR [rsi+r11*1+496], xmm12
	vmovdqu ymm0, YMMWORD PTR [rcx]
	vmovdqu ymm1, YMMWORD PTR [rcx+32]
	vmovdqu ymm2, YMMWORD PTR [rcx+64]
	vmovdqu ymm3, YMMWORD PTR [rcx+96]
	vpunpckldq ymm12, ymm0, ymm1
	vpunpckhdq ymm13, ymm0, ymm1
	vpunpckldq ymm14, ymm2, ymm3
	vpunpckhdq ymm15, ymm2, ymm3
	vpunpcklqdq ymm0, ymm12, ymm14
	vpunpckhqdq ymm1, ymm12, ymm14
	vpunpcklqdq ymm2, ymm13, ymm15
	vpunpckhqdq ymm3, ymm13, ymm15
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+32]
	vpaddd ymm0, ymm0, ymm14
	vpaddd ymm1, ymm1, ymm14
	vpaddd ymm2, ymm2, ymm14
	vpaddd ymm3, ymm3, ymm14
	vpxor xmm12, xmm0, XMMWORD PTR [rsi+32]
	vmovdqu XMMWORD PTR [rsi+r11*1+32], xmm12
	vextracti128 xmm13, ymm0, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+288]
	vmovdqu XMMWORD PTR [rsi+r11*1+288], xmm12
	vpxor xmm12, xmm1, XMMWORD PTR [rsi+96]
	vmovdqu XMMWORD PTR [rsi+r11*1+96], xmm12
	vextracti128 xmm13, ymm1, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+352]
	vmovdqu XMMWORD PTR [rsi+r11*1+352], xmm12
	vpxor xmm12, xmm2, XMMWORD PTR [rsi+160]
	vmovdqu XMMWORD PTR [rsi+r11*1+160], xmm12
	vextracti128 xmm13, ymm2, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+416]
	vmovdqu XMMWORD PTR [rsi+r11*1+416], xmm12
	vpxor xmm12, xmm3, XMMWORD PTR [rsi+224]
	vmovdqu XMMWORD PTR [rsi+r11*1+224], xmm12
	vextracti128 xmm13, ymm3, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+480]
	vmovdqu XMMWORD PTR [rsi+r11*1+480], xmm12
	mov eax, DWORD PTR [rdi+48]
	add eax, 8
	mov DWORD PTR [rdi+48], eax
	add rsi, 512
	sub rdx, 512
	cmp rdx, 512
	jae 24b
	jmp 23f
22:
23:
	cmp rdx, 385
	jb 25f
	vbroadcasti128 ymm12, XMMWORD PTR [rdi]
	vpshufd ymm0, ymm12, 0
	vpshufd ymm1, ymm12, 85
	vpshufd ymm2, ymm12, 170
	vpshufd ymm3, ymm12, 255
	vbroadcasti128 ymm12, XMMWORD PTR [rdi+16]
	vpshufd ymm4, ymm12, 0
	vpshufd ymm5, ymm12, 85
	vpshufd ymm6, ymm12, 170
	vpshufd ymm7, ymm12, 255
	vbroadcasti128 ymm12, XMMWORD PTR [rdi+48]
	vpshufd ymm8, ymm12, 0
	vpshufd ymm9, ymm12, 85
	vpshufd ymm10, ymm12, 170
	vpshufd ymm11, ymm12, 255
	vmovdqu ymm13, YMMWORD PTR [rcx+192]
	vpaddd ymm8, ymm8, ymm13
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+32]
	vpshufd ymm12, ymm14, 0
	vpshufd ymm13, ymm14, 85
	vpshufd ymm15, ymm14, 170
	vmovdqu YMMWORD PTR [rcx+64], ymm15
	vpshufd ymm15, ymm14, 255
	vmovdqu YMMWORD PTR [rcx+96], ymm15
	vmovdqu ymm15, YMMWORD PTR [rcx+128]
	vmovdqu ymm14, YMMWORD PTR [rcx+64]
	vmovdqu ymm15, YMMWORD PTR [rcx+96]
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 16
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 12
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vprold ymm8, ymm8, 8
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vprold ymm4, ymm4, 7
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 16
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 12
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vprold ymm9, ymm9, 8
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vprold ymm5, ymm5, 7
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 16
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 12
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vprold ymm10, ymm10, 8
	vpaddd ymm14, ymm14, ymm10
	vpxor ymm6, ymm6, ymm14
	vprold ymm6, ymm6, 7
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 16
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 12
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vprold ymm11, ymm11, 8
	vpaddd ymm15, ymm15, ymm11
	vpxor ymm7, ymm7, ymm15
	vprold ymm7, ymm7, 7
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 16
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vprold ymm11, ymm11, 8
	vpaddd ymm14, ymm14, ymm11
	vpxor ymm5, ymm5, ymm14
	vprold ymm5, ymm5, 7
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 16
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 12
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vprold ymm8, ymm8, 8
	vpaddd ymm15, ymm15, ymm8
	vpxor ymm6, ymm6, ymm15
	vprold ymm6, ymm6, 7
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 16
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 12
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vprold ymm9, ymm9, 8
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vprold ymm7, ymm7, 7
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 16
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 12
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vprold ymm10, ymm10, 8
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vprold ymm4, ymm4, 7
	vmovdqu YMMWORD PTR [rcx+64], ymm14
	vmovdqu YMMWORD PTR [rcx+96], ymm15
	vmovdqu ymm15, YMMWORD PTR [rcx+128]
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vpunpckldq ymm12, ymm0, ymm1
	vpunpckhdq ymm13, ymm0, ymm1
	vpunpckldq ymm14, ymm2, ymm3
	vpunpckhdq ymm15, ymm2, ymm3
	vpunpcklqdq ymm0, ymm12, ymm14
	vpunpckhqdq ymm1, ymm12, ymm14
	vpunpcklqdq ymm2, ymm13, ymm15
	vpunpckhqdq ymm3, ymm13, ymm15
	vbroadcasti128 ymm14, XMMWORD PTR [rdi]
	vpaddd ymm0, ymm0, ymm14
	vpaddd ymm1, ymm1, ymm14
	vpaddd ymm2, ymm2, ymm14
	vpaddd ymm3, ymm3, ymm14
	vpxor xmm12, xmm0, XMMWORD PTR [rsi]
	vmovdqu XMMWORD PTR [rsi+r11*1], xmm12
	vextracti128 xmm13, ymm0, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+256]
	vmovdqu XMMWORD PTR [rsi+r11*1+256], xmm12
	vpxor xmm12, xmm1, XMMWORD PTR [rsi+64]
	vmovdqu XMMWORD PTR [rsi+r11*1+64], xmm12
	vextracti128 xmm13, ymm1, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+320]
	vmovdqu XMMWORD PTR [rsi+r11*1+320], xmm12
	vpxor xmm12, xmm2, XMMWORD PTR [rsi+128]
	vmovdqu XMMWORD PTR [rsi+r11*1+128], xmm12
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+128], xmm13
	vpxor xmm12, xmm3, XMMWORD PTR [rsi+192]
	vmovdqu XMMWORD PTR [rsi+r11*1+192], xmm12
	vextracti128 xmm13, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+224], xmm13
	vpunpckldq ymm12, ymm4, ymm5
	vpunpckhdq ymm13, ymm4, ymm5
	vpunpckldq ymm14, ymm6, ymm7
	vpunpckhdq ymm15, ymm6, ymm7
	vpunpcklqdq ymm4, ymm12, ymm14
	vpunpckhqdq ymm5, ymm12, ymm14
	vpunpcklqdq ymm6, ymm13, ymm15
	vpunpckhqdq ymm7, ymm13, ymm15
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+16]
	vpaddd ymm4, ymm4, ymm14
	vpaddd ymm5, ymm5, ymm14
	vpaddd ymm6, ymm6, ymm14
	vpaddd ymm7, ymm7, ymm14
	vpxor xmm12, xmm4, XMMWORD PTR [rsi+16]
	vmovdqu XMMWORD PTR [rsi+r11*1+16], xmm12
	vextracti128 xmm13, ymm4, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+272]
	vmovdqu XMMWORD PTR [rsi+r11*1+272], xmm12
	vpxor xmm12, xmm5, XMMWORD PTR [rsi+80]
	vmovdqu XMMWORD PTR [rsi+r11*1+80], xmm12
	vextracti128 xmm13, ymm5, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+336]
	vmovdqu XMMWORD PTR [rsi+r11*1+336], xmm12
	vpxor xmm12, xmm6, XMMWORD PTR [rsi+144]
	vmovdqu XMMWORD PTR [rsi+r11*1+144], xmm12
	vextracti128 xmm13, ymm6, 1
	vmovdqu XMMWORD PTR [rcx+144], xmm13
	vpxor xmm12, xmm7, XMMWORD PTR [rsi+208]
	vmovdqu XMMWORD PTR [rsi+r11*1+208], xmm12
	vextracti128 xmm13, ymm7, 1
	vmovdqu XMMWORD PTR [rcx+240], xmm13
	vmovdqu ymm15, YMMWORD PTR [rcx+192]
	vpaddd ymm8, ymm8, ymm15
	vpunpckldq ymm12, ymm8, ymm9
	vpunpckhdq ymm13, ymm8, ymm9
	vpunpckldq ymm14, ymm10, ymm11
	vpunpckhdq ymm15, ymm10, ymm11
	vpunpcklqdq ymm8, ymm12, ymm14
	vpunpckhqdq ymm9, ymm12, ymm14
	vpunpcklqdq ymm10, ymm13, ymm15
	vpunpckhqdq ymm11, ymm13, ymm15
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+48]
	vpaddd ymm8, ymm8, ymm14
	vpaddd ymm9, ymm9, ymm14
	vpaddd ymm10, ymm10, ymm14
	vpaddd ymm11, ymm11, ymm14
	vpxor xmm12, xmm8, XMMWORD PTR [rsi+48]
	vmovdqu XMMWORD PTR [rsi+r11*1+48], xmm12
	vextracti128 xmm13, ymm8, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+304]
	vmovdqu XMMWORD PTR [rsi+r11*1+304], xmm12
	vpxor xmm12, xmm9, XMMWORD PTR [rsi+112]
	vmovdqu XMMWORD PTR [rsi+r11*1+112], xmm12
	vextracti128 xmm13, ymm9, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+368]
	vmovdqu XMMWORD PTR [rsi+r11*1+368], xmm12
	vpxor xmm12, xmm10, XMMWORD PTR [rsi+176]
	vmovdqu XMMWORD PTR [rsi+r11*1+176], xmm12
	vextracti128 xmm13, ymm10, 1
	vmovdqu XMMWORD PTR [rcx+176], xmm13
	vpxor xmm12, xmm11, XMMWORD PTR [rsi+240]
	vmovdqu XMMWORD PTR [rsi+r11*1+240], xmm12
	vextracti128 xmm13, ymm11, 1
	vmovdqu XMMWORD PTR [rcx+272], xmm13
	vmovdqu ymm0, YMMWORD PTR [rcx]
	vmovdqu ymm1, YMMWORD PTR [rcx+32]
	vmovdqu ymm2, YMMWORD PTR [rcx+64]
	vmovdqu ymm3, YMMWORD PTR [rcx+96]
	vpunpckldq ymm12, ymm0, ymm1
	vpunpckhdq ymm13, ymm0, ymm1
	vpunpckldq ymm14, ymm2, ymm3
	vpunpckhdq ymm15, ymm2, ymm3
	vpunpcklqdq ymm0, ymm12, ymm14
	vpunpckhqdq ymm1, ymm12, ymm14
	vpunpcklqdq ymm2, ymm13, ymm15
	vpunpckhqdq ymm3, ymm13, ymm15
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+32]
	vpaddd ymm0, ymm0, ymm14
	vpaddd ymm1, ymm1, ymm14
	vpaddd ymm2, ymm2, ymm14
	vpaddd ymm3, ymm3, ymm14
	vpxor xmm12, xmm0, XMMWORD PTR [rsi+32]
	vmovdqu XMMWORD PTR [rsi+r11*1+32], xmm12
	vextracti128 xmm13, ymm0, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+288]
	vmovdqu XMMWORD PTR [rsi+r11*1+288], xmm12
	vpxor xmm12, xmm1, XMMWORD PTR [rsi+96]
	vmovdqu XMMWORD PTR [rsi+r11*1+96], xmm12
	vextracti128 xmm13, ymm1, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+352]
	vmovdqu XMMWORD PTR [rsi+r11*1+352], xmm12
	vpxor xmm12, xmm2, XMMWORD PTR [rsi+160]
	vmovdqu XMMWORD PTR [rsi+r11*1+160], xmm12
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+160], xmm13
	vpxor xmm12, xmm3, XMMWORD PTR [rsi+224]
	vmovdqu XMMWORD PTR [rsi+r11*1+224], xmm12
	vextracti128 xmm13, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+256], xmm13
	vmovdqu ymm12, YMMWORD PTR [rcx+128]
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu ymm12, YMMWORD PTR [rcx+160]
	vmovdqu YMMWORD PTR [rcx+32], ymm12
	vmovdqu ymm12, YMMWORD PTR [rcx+224]
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu ymm12, YMMWORD PTR [rcx+256]
	vmovdqu YMMWORD PTR [rcx+96], ymm12
	mov r9, rcx
	add rsi, 384
	sub rdx, 384
	mov r10, r11
	add r10, rsi
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 27f
29:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [r10+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 29b
	jmp 28f
27:
28:
	cmp rcx, rdx
	je 210f
212:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [r10+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 212b
	jmp 211f
210:
211:
	vzeroupper
	mov rsi, r9
	jmp 26f
25:
	mov r9, rcx
	cmp rdx, 257
	jb 213f
	vmovdqu ymm14, YMMWORD PTR [r9+128]
	vmovdqu ymm15, YMMWORD PTR [r9+160]
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vmovdqu ymm13, YMMWORD PTR [r9+256]
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vbroadcasti128 ymm1, XMMWORD PTR [rdi+16]
	vbroadcasti128 ymm2, XMMWORD PTR [rdi+32]
	vbroadcasti128 ymm3, XMMWORD PTR [rdi+48]
	vpor ymm4, ymm0, ymm0
	vpor ymm5, ymm1, ymm1
	vpor ymm6, ymm2, ymm2
	vpor ymm8, ymm0, ymm0
	vpor ymm9, ymm1, ymm1
	vpor ymm10, ymm2, ymm2
	vperm2i128 ymm11, ymm13, ymm13, 0
	vpaddd ymm11, ymm11, ymm13
	vpaddd ymm11, ymm11, ymm3
	vpaddd ymm7, ymm3, ymm13
	vpaddd ymm3, ymm3, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpshufd ymm9, ymm9, 57
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vprold ymm11, ymm11, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vprold ymm9, ymm9, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vprold ymm11, ymm11, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vprold ymm9, ymm9, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpshufd ymm9, ymm9, 147
	vpshufd ymm10, ymm10, 78
	vpshufd ymm11, ymm11, 57
	vbroadcasti128 ymm14, XMMWORD PTR [rdi]
	vpaddd ymm0, ymm0, ymm14
	vpaddd ymm4, ymm4, ymm14
	vpaddd ymm8, ymm8, ymm14
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+16]
	vpaddd ymm1, ymm1, ymm14
	vpaddd ymm5, ymm5, ymm14
	vpaddd ymm9, ymm9, ymm14
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+32]
	vpaddd ymm2, ymm2, ymm14
	vpaddd ymm6, ymm6, ymm14
	vpaddd ymm10, ymm10, ymm14
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vmovdqu ymm13, YMMWORD PTR [r9+256]
	vbroadcasti128 ymm14, XMMWORD PTR [rdi+48]
	vpaddd ymm15, ymm14, ymm12
	vpaddd ymm3, ymm3, ymm15
	vpaddd ymm15, ymm14, ymm13
	vpaddd ymm7, ymm7, ymm15
	vperm2i128 ymm15, ymm13, ymm13, 0
	vpaddd ymm15, ymm15, ymm13
	vpaddd ymm15, ymm15, ymm14
	vpaddd ymm11, ymm11, ymm15
	vperm2i128 ymm12, ymm0, ymm1, 32
	vmovdqu ymm13, YMMWORD PTR [rsi]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+r11*1], ymm13
	vperm2i128 ymm12, ymm2, ymm3, 32
	vmovdqu ymm13, YMMWORD PTR [rsi+32]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+r11*1+32], ymm13
	vperm2i128 ymm12, ymm0, ymm1, 49
	vmovdqu ymm13, YMMWORD PTR [rsi+64]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+r11*1+64], ymm13
	vperm2i128 ymm12, ymm2, ymm3, 49
	vmovdqu ymm13, YMMWORD PTR [rsi+96]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+r11*1+96], ymm13
	vperm2i128 ymm12, ymm4, ymm5, 32
	vmovdqu ymm13, YMMWORD PTR [rsi+128]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+r11*1+128], ymm13
	vperm2i128 ymm12, ymm6, ymm7, 32
	vmovdqu ymm13, YMMWORD PTR [rsi+160]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+r11*1+160], ymm13
	vperm2i128 ymm12, ymm4, ymm5, 49
	vmovdqu ymm13, YMMWORD PTR [rsi+192]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+r11*1+192], ymm13
	vperm2i128 ymm12, ymm6, ymm7, 49
	vmovdqu ymm13, YMMWORD PTR [rsi+224]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+r11*1+224], ymm13
	vperm2i128 ymm12, ymm8, ymm9, 32
	vmovdqu YMMWORD PTR [r9], ymm12
	vperm2i128 ymm12, ymm10, ymm11, 32
	vmovdqu YMMWORD PTR [r9+32], ymm12
	vperm2i128 ymm12, ymm8, ymm9, 49
	vmovdqu YMMWORD PTR [r9+64], ymm12
	vperm2i128 ymm12, ymm10, ymm11, 49
	vmovdqu YMMWORD PTR [r9+96], ymm12
	add rsi, 256
	sub rdx, 256
	mov r10, r11
	add r10, rsi
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 215f
217:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [r10+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 217b
	jmp 216f
215:
216:
	cmp rcx, rdx
	je 218f
220:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [r10+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 220b
	jmp 219f
218:
219:
	jmp 214f
213:
	cmp rdx, 129
	jb 221f
	vmovdqu ymm8, YMMWORD PTR [r9+128]
	vmovdqu ymm9, YMMWORD PTR [r9+160]
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vmovdqu ymm13, YMMWORD PTR [r9+256]
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vbroadcasti128 ymm1, XMMWORD PTR [rdi+16]
	vbroadcasti128 ymm2, XMMWORD PTR [rdi+32]
	vbroadcasti128 ymm3, XMMWORD PTR [rdi+48]
	vpor ymm4, ymm0, ymm0
	vpor ymm5, ymm1, ymm1
	vpor ymm6, ymm2, ymm2
	vpaddd ymm7, ymm3, ymm13
	vpaddd ymm3, ymm3, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpshufd ymm5, ymm5, 57
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 147
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 16
	vprold ymm7, ymm7, 16
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 12
	vprold ymm5, ymm5, 12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vprold ymm3, ymm3, 8
	vprold ymm7, ymm7, 8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vprold ymm1, ymm1, 7
	vprold ymm5, ymm5, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vmovdqu ymm13, YMMWORD PTR [r9+256]
	vbroadcasti128 ymm10, XMMWORD PTR [rdi]
	vpaddd ymm0, ymm0, ymm10
	vpaddd ymm4, ymm4, ymm10
	vbroadcasti128 ymm10, XMMWORD PTR [rdi+16]
	vpaddd ymm1, ymm1, ymm10
	vpaddd ymm5, ymm5, ymm10
	vbroadcasti128 ymm10, XMMWORD PTR [rdi+32]
	vpaddd ymm2, ymm2, ymm10
	vpaddd ymm6, ymm6, ymm10
	vbroadcasti128 ymm10, XMMWORD PTR [rdi+48]
	vpaddd ymm11, ymm10, ymm12
	vpaddd ymm3, ymm3, ymm11
	vpaddd ymm11, ymm10, ymm13
	vpaddd ymm7, ymm7, ymm11
	vperm2i128 ymm10, ymm0, ymm1, 32
	vmovdqu YMMWORD PTR [r9], ymm10
	vperm2i128 ymm10, ymm2, ymm3, 32
	vmovdqu YMMWORD PTR [r9+32], ymm10
	vperm2i128 ymm10, ymm0, ymm1, 49
	vmovdqu YMMWORD PTR [r9+64], ymm10
	vperm2i128 ymm10, ymm2, ymm3, 49
	vmovdqu YMMWORD PTR [r9+96], ymm10
	vperm2i128 ymm10, ymm4, ymm5, 32
	vmovdqu YMMWORD PTR [r9+128], ymm10
	vperm2i128 ymm10, ymm6, ymm7, 32
	vmovdqu YMMWORD PTR [r9+160], ymm10
	vperm2i128 ymm10, ymm4, ymm5, 49
	vmovdqu YMMWORD PTR [r9+192], ymm10
	vperm2i128 ymm10, ymm6, ymm7, 49
	vmovdqu YMMWORD PTR [r9+224], ymm10
	mov r10, r11
	add r10, rsi
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 223f
225:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [r10+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 225b
	jmp 224f
223:
224:
	cmp rcx, rdx
	je 226f
228:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [r10+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 228b
	jmp 227f
226:
227:
	jmp 222f
221:
	test rdx, rdx
	je 229f
	vmovdqu ymm8, YMMWORD PTR [r9+128]
	vmovdqu ymm9, YMMWORD PTR [r9+160]
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vbroadcasti128 ymm1, XMMWORD PTR [rdi+16]
	vbroadcasti128 ymm2, XMMWORD PTR [rdi+32]
	vbroadcasti128 ymm3, XMMWORD PTR [rdi+48]
	vpaddd ymm3, ymm3, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 16
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprold ymm3, ymm3, 8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprold ymm1, ymm1, 7
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vbroadcasti128 ymm10, XMMWORD PTR [rdi]
	vpaddd ymm0, ymm0, ymm10
	vbroadcasti128 ymm10, XMMWORD PTR [rdi+16]
	vpaddd ymm1, ymm1, ymm10
	vbroadcasti128 ymm10, XMMWORD PTR [rdi+32]
	vpaddd ymm2, ymm2, ymm10
	vbroadcasti128 ymm10, XMMWORD PTR [rdi+48]
	vpaddd ymm11, ymm10, ymm12
	vpaddd ymm3, ymm3, ymm11
	vperm2i128 ymm10, ymm0, ymm1, 32
	vmovdqu YMMWORD PTR [r9], ymm10
	vperm2i128 ymm10, ymm2, ymm3, 32
	vmovdqu YMMWORD PTR [r9+32], ymm10
	vperm2i128 ymm10, ymm0, ymm1, 49
	vmovdqu YMMWORD PTR [r9+64], ymm10
	vperm2i128 ymm10, ymm2, ymm3, 49
	vmovdqu YMMWORD PTR [r9+96], ymm10
	mov r10, r11
	add r10, rsi
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 231f
233:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [r10+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 233b
	jmp 232f
231:
232:
	cmp rcx, rdx
	je 234f
236:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [r10+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 236b
	jmp 235f
234:
235:
	jmp 230f
229:
230:
222:
214:
	vzeroupper
	mov rsi, r9
26:
21:
	ret
	.p2align 6
