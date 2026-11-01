// The functions of `src/internal/vg_chacha20_xor_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor_avx2:
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
	cmp rdx, 512
	jb 20f
22:
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
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
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
	vmovdqu XMMWORD PTR [rsi], xmm12
	vextracti128 xmm13, ymm0, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+256]
	vmovdqu XMMWORD PTR [rsi+256], xmm12
	vpxor xmm12, xmm1, XMMWORD PTR [rsi+64]
	vmovdqu XMMWORD PTR [rsi+64], xmm12
	vextracti128 xmm13, ymm1, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+320]
	vmovdqu XMMWORD PTR [rsi+320], xmm12
	vpxor xmm12, xmm2, XMMWORD PTR [rsi+128]
	vmovdqu XMMWORD PTR [rsi+128], xmm12
	vextracti128 xmm13, ymm2, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+384]
	vmovdqu XMMWORD PTR [rsi+384], xmm12
	vpxor xmm12, xmm3, XMMWORD PTR [rsi+192]
	vmovdqu XMMWORD PTR [rsi+192], xmm12
	vextracti128 xmm13, ymm3, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+448]
	vmovdqu XMMWORD PTR [rsi+448], xmm12
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
	vmovdqu XMMWORD PTR [rsi+16], xmm12
	vextracti128 xmm13, ymm4, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+272]
	vmovdqu XMMWORD PTR [rsi+272], xmm12
	vpxor xmm12, xmm5, XMMWORD PTR [rsi+80]
	vmovdqu XMMWORD PTR [rsi+80], xmm12
	vextracti128 xmm13, ymm5, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+336]
	vmovdqu XMMWORD PTR [rsi+336], xmm12
	vpxor xmm12, xmm6, XMMWORD PTR [rsi+144]
	vmovdqu XMMWORD PTR [rsi+144], xmm12
	vextracti128 xmm13, ymm6, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+400]
	vmovdqu XMMWORD PTR [rsi+400], xmm12
	vpxor xmm12, xmm7, XMMWORD PTR [rsi+208]
	vmovdqu XMMWORD PTR [rsi+208], xmm12
	vextracti128 xmm13, ymm7, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+464]
	vmovdqu XMMWORD PTR [rsi+464], xmm12
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
	vmovdqu XMMWORD PTR [rsi+48], xmm12
	vextracti128 xmm13, ymm8, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+304]
	vmovdqu XMMWORD PTR [rsi+304], xmm12
	vpxor xmm12, xmm9, XMMWORD PTR [rsi+112]
	vmovdqu XMMWORD PTR [rsi+112], xmm12
	vextracti128 xmm13, ymm9, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+368]
	vmovdqu XMMWORD PTR [rsi+368], xmm12
	vpxor xmm12, xmm10, XMMWORD PTR [rsi+176]
	vmovdqu XMMWORD PTR [rsi+176], xmm12
	vextracti128 xmm13, ymm10, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+432]
	vmovdqu XMMWORD PTR [rsi+432], xmm12
	vpxor xmm12, xmm11, XMMWORD PTR [rsi+240]
	vmovdqu XMMWORD PTR [rsi+240], xmm12
	vextracti128 xmm13, ymm11, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+496]
	vmovdqu XMMWORD PTR [rsi+496], xmm12
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
	vmovdqu XMMWORD PTR [rsi+32], xmm12
	vextracti128 xmm13, ymm0, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+288]
	vmovdqu XMMWORD PTR [rsi+288], xmm12
	vpxor xmm12, xmm1, XMMWORD PTR [rsi+96]
	vmovdqu XMMWORD PTR [rsi+96], xmm12
	vextracti128 xmm13, ymm1, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+352]
	vmovdqu XMMWORD PTR [rsi+352], xmm12
	vpxor xmm12, xmm2, XMMWORD PTR [rsi+160]
	vmovdqu XMMWORD PTR [rsi+160], xmm12
	vextracti128 xmm13, ymm2, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+416]
	vmovdqu XMMWORD PTR [rsi+416], xmm12
	vpxor xmm12, xmm3, XMMWORD PTR [rsi+224]
	vmovdqu XMMWORD PTR [rsi+224], xmm12
	vextracti128 xmm13, ymm3, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+480]
	vmovdqu XMMWORD PTR [rsi+480], xmm12
	mov eax, DWORD PTR [rdi+48]
	add eax, 8
	mov DWORD PTR [rdi+48], eax
	add rsi, 512
	sub rdx, 512
	cmp rdx, 512
	jae 22b
	jmp 21f
20:
21:
	cmp rdx, 385
	jb 23f
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
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm8, ymm8, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm12, ymm12, ymm8
	vpxor ymm4, ymm4, ymm12
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm5
	vpxor ymm9, ymm9, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm13, ymm13, ymm9
	vpxor ymm5, ymm5, ymm13
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx+64]
	vmovdqu ymm13, YMMWORD PTR [rcx+96]
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm2, ymm2, ymm6
	vpxor ymm10, ymm10, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm12, ymm12, ymm10
	vpxor ymm6, ymm6, ymm12
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm7
	vpxor ymm11, ymm11, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm13, ymm13, ymm11
	vpxor ymm7, ymm7, ymm13
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm14
	vpaddd ymm0, ymm0, ymm5
	vpxor ymm11, ymm11, ymm0
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm12, ymm12, ymm11
	vpxor ymm5, ymm5, ymm12
	vpslld ymm14, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vpshufb ymm8, ymm8, ymm15
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 12
	vpsrld ymm6, ymm6, 20
	vpor ymm6, ymm6, ymm14
	vpaddd ymm1, ymm1, ymm6
	vpxor ymm8, ymm8, ymm1
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm8, ymm8, ymm14
	vpaddd ymm13, ymm13, ymm8
	vpxor ymm6, ymm6, ymm13
	vpslld ymm14, ymm6, 7
	vpsrld ymm6, ymm6, 25
	vpor ymm6, ymm6, ymm14
	vmovdqu YMMWORD PTR [rcx+64], ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm13
	vmovdqu ymm12, YMMWORD PTR [rcx]
	vmovdqu ymm13, YMMWORD PTR [rcx+32]
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vpshufb ymm9, ymm9, ymm15
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 12
	vpsrld ymm7, ymm7, 20
	vpor ymm7, ymm7, ymm14
	vpaddd ymm2, ymm2, ymm7
	vpxor ymm9, ymm9, ymm2
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm9, ymm9, ymm14
	vpaddd ymm12, ymm12, ymm9
	vpxor ymm7, ymm7, ymm12
	vpslld ymm14, ymm7, 7
	vpsrld ymm7, ymm7, 25
	vpor ymm7, ymm7, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vpshufb ymm10, ymm10, ymm15
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 12
	vpsrld ymm4, ymm4, 20
	vpor ymm4, ymm4, ymm14
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm10, ymm10, ymm3
	vmovdqu ymm14, YMMWORD PTR [rcx+160]
	vpshufb ymm10, ymm10, ymm14
	vpaddd ymm13, ymm13, ymm10
	vpxor ymm4, ymm4, ymm13
	vpslld ymm14, ymm4, 7
	vpsrld ymm4, ymm4, 25
	vpor ymm4, ymm4, ymm14
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
	vmovdqu XMMWORD PTR [rsi], xmm12
	vextracti128 xmm13, ymm0, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+256]
	vmovdqu XMMWORD PTR [rsi+256], xmm12
	vpxor xmm12, xmm1, XMMWORD PTR [rsi+64]
	vmovdqu XMMWORD PTR [rsi+64], xmm12
	vextracti128 xmm13, ymm1, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+320]
	vmovdqu XMMWORD PTR [rsi+320], xmm12
	vpxor xmm12, xmm2, XMMWORD PTR [rsi+128]
	vmovdqu XMMWORD PTR [rsi+128], xmm12
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+128], xmm13
	vpxor xmm12, xmm3, XMMWORD PTR [rsi+192]
	vmovdqu XMMWORD PTR [rsi+192], xmm12
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
	vmovdqu XMMWORD PTR [rsi+16], xmm12
	vextracti128 xmm13, ymm4, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+272]
	vmovdqu XMMWORD PTR [rsi+272], xmm12
	vpxor xmm12, xmm5, XMMWORD PTR [rsi+80]
	vmovdqu XMMWORD PTR [rsi+80], xmm12
	vextracti128 xmm13, ymm5, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+336]
	vmovdqu XMMWORD PTR [rsi+336], xmm12
	vpxor xmm12, xmm6, XMMWORD PTR [rsi+144]
	vmovdqu XMMWORD PTR [rsi+144], xmm12
	vextracti128 xmm13, ymm6, 1
	vmovdqu XMMWORD PTR [rcx+144], xmm13
	vpxor xmm12, xmm7, XMMWORD PTR [rsi+208]
	vmovdqu XMMWORD PTR [rsi+208], xmm12
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
	vmovdqu XMMWORD PTR [rsi+48], xmm12
	vextracti128 xmm13, ymm8, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+304]
	vmovdqu XMMWORD PTR [rsi+304], xmm12
	vpxor xmm12, xmm9, XMMWORD PTR [rsi+112]
	vmovdqu XMMWORD PTR [rsi+112], xmm12
	vextracti128 xmm13, ymm9, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+368]
	vmovdqu XMMWORD PTR [rsi+368], xmm12
	vpxor xmm12, xmm10, XMMWORD PTR [rsi+176]
	vmovdqu XMMWORD PTR [rsi+176], xmm12
	vextracti128 xmm13, ymm10, 1
	vmovdqu XMMWORD PTR [rcx+176], xmm13
	vpxor xmm12, xmm11, XMMWORD PTR [rsi+240]
	vmovdqu XMMWORD PTR [rsi+240], xmm12
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
	vmovdqu XMMWORD PTR [rsi+32], xmm12
	vextracti128 xmm13, ymm0, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+288]
	vmovdqu XMMWORD PTR [rsi+288], xmm12
	vpxor xmm12, xmm1, XMMWORD PTR [rsi+96]
	vmovdqu XMMWORD PTR [rsi+96], xmm12
	vextracti128 xmm13, ymm1, 1
	vpxor xmm12, xmm13, XMMWORD PTR [rsi+352]
	vmovdqu XMMWORD PTR [rsi+352], xmm12
	vpxor xmm12, xmm2, XMMWORD PTR [rsi+160]
	vmovdqu XMMWORD PTR [rsi+160], xmm12
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+160], xmm13
	vpxor xmm12, xmm3, XMMWORD PTR [rsi+224]
	vmovdqu XMMWORD PTR [rsi+224], xmm12
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
	mov r10, rsi
	mov rsi, r9
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 25f
27:
	vmovdqu ymm0, YMMWORD PTR [r10+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [r10+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 27b
	jmp 26f
25:
26:
	mov rdi, r10
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 28f
210:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	cmp rcx, rdx
	je 211f
213:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 213b
	jmp 212f
211:
212:
	vzeroupper
	mov rsi, r9
	jmp 24f
23:
	mov r9, rcx
	cmp rdx, 257
	jb 214f
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vpshufb ymm3, ymm3, ymm14
	vpshufb ymm7, ymm7, ymm14
	vpshufb ymm11, ymm11, ymm14
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 12
	vpsrld ymm9, ymm9, 20
	vpor ymm9, ymm9, ymm12
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpaddd ymm8, ymm8, ymm9
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpxor ymm11, ymm11, ymm8
	vpshufb ymm3, ymm3, ymm15
	vpshufb ymm7, ymm7, ymm15
	vpshufb ymm11, ymm11, ymm15
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpaddd ymm10, ymm10, ymm11
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpxor ymm9, ymm9, ymm10
	vpslld ymm12, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm12
	vpslld ymm13, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm13
	vpslld ymm12, ymm9, 7
	vpsrld ymm9, ymm9, 25
	vpor ymm9, ymm9, ymm12
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
	vmovdqu YMMWORD PTR [rsi], ymm13
	vperm2i128 ymm12, ymm2, ymm3, 32
	vmovdqu ymm13, YMMWORD PTR [rsi+32]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+32], ymm13
	vperm2i128 ymm12, ymm0, ymm1, 49
	vmovdqu ymm13, YMMWORD PTR [rsi+64]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vperm2i128 ymm12, ymm2, ymm3, 49
	vmovdqu ymm13, YMMWORD PTR [rsi+96]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+96], ymm13
	vperm2i128 ymm12, ymm4, ymm5, 32
	vmovdqu ymm13, YMMWORD PTR [rsi+128]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+128], ymm13
	vperm2i128 ymm12, ymm6, ymm7, 32
	vmovdqu ymm13, YMMWORD PTR [rsi+160]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+160], ymm13
	vperm2i128 ymm12, ymm4, ymm5, 49
	vmovdqu ymm13, YMMWORD PTR [rsi+192]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+192], ymm13
	vperm2i128 ymm12, ymm6, ymm7, 49
	vmovdqu ymm13, YMMWORD PTR [rsi+224]
	vpxor ymm13, ymm13, ymm12
	vmovdqu YMMWORD PTR [rsi+224], ymm13
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
	mov r10, rsi
	mov rsi, r9
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 216f
218:
	vmovdqu ymm0, YMMWORD PTR [r10+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [r10+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 218b
	jmp 217f
216:
217:
	mov rdi, r10
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 219f
221:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 221b
	jmp 220f
219:
220:
	cmp rcx, rdx
	je 222f
224:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 224b
	jmp 223f
222:
223:
	jmp 215f
214:
	cmp rdx, 129
	jb 225f
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	vpshufb ymm3, ymm3, ymm8
	vpshufb ymm7, ymm7, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 12
	vpsrld ymm5, ymm5, 20
	vpor ymm5, ymm5, ymm11
	vpaddd ymm0, ymm0, ymm1
	vpaddd ymm4, ymm4, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm7, ymm7, ymm4
	vpshufb ymm3, ymm3, ymm9
	vpshufb ymm7, ymm7, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm6, ymm6, ymm7
	vpxor ymm1, ymm1, ymm2
	vpxor ymm5, ymm5, ymm6
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpslld ymm11, ymm5, 7
	vpsrld ymm5, ymm5, 25
	vpor ymm5, ymm5, ymm11
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
	mov r10, rsi
	mov rsi, r9
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 227f
229:
	vmovdqu ymm0, YMMWORD PTR [r10+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [r10+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 229b
	jmp 228f
227:
228:
	mov rdi, r10
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 230f
232:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 232b
	jmp 231f
230:
231:
	cmp rcx, rdx
	je 233f
235:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 235b
	jmp 234f
233:
234:
	jmp 226f
225:
	test rdx, rdx
	je 236f
	cmp rdx, 65
	jb 238f
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
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	vpshufd ymm1, ymm1, 57
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 147
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
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
	mov r10, rsi
	mov rsi, r9
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 240f
242:
	vmovdqu ymm0, YMMWORD PTR [r10+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [r10+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 242b
	jmp 241f
240:
241:
	mov rdi, r10
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 243f
245:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 245b
	jmp 244f
243:
244:
	cmp rcx, rdx
	je 246f
248:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 248b
	jmp 247f
246:
247:
	jmp 239f
238:
	vzeroupper
	call {vg_chacha20_xor}
	mov r9, rsi
239:
	jmp 237f
236:
237:
226:
215:
	vzeroupper
	mov rsi, r9
24:
	ret
	.p2align 6
