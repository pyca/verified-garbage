// The functions of `src/internal/vg_chacha20_xor_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor_avx512:
	movabs rax, 0
	mov QWORD PTR [rcx+256], rax
	movabs rax, 0
	mov QWORD PTR [rcx+264], rax
	movabs rax, 1
	mov QWORD PTR [rcx+272], rax
	movabs rax, 0
	mov QWORD PTR [rcx+280], rax
	movabs rax, 2
	mov QWORD PTR [rcx+288], rax
	movabs rax, 0
	mov QWORD PTR [rcx+296], rax
	movabs rax, 3
	mov QWORD PTR [rcx+304], rax
	movabs rax, 0
	mov QWORD PTR [rcx+312], rax
	movabs rax, 4
	mov QWORD PTR [rcx+192], rax
	movabs rax, 0
	mov QWORD PTR [rcx+200], rax
	movabs rax, 5
	mov QWORD PTR [rcx+208], rax
	movabs rax, 0
	mov QWORD PTR [rcx+216], rax
	movabs rax, 6
	mov QWORD PTR [rcx+224], rax
	movabs rax, 0
	mov QWORD PTR [rcx+232], rax
	movabs rax, 7
	mov QWORD PTR [rcx+240], rax
	movabs rax, 0
	mov QWORD PTR [rcx+248], rax
	movabs rax, 4294967296
	mov QWORD PTR [rcx+128], rax
	movabs rax, 12884901890
	mov QWORD PTR [rcx+136], rax
	movabs rax, 21474836484
	mov QWORD PTR [rcx+144], rax
	movabs rax, 30064771078
	mov QWORD PTR [rcx+152], rax
	movabs rax, 38654705672
	mov QWORD PTR [rcx+160], rax
	movabs rax, 47244640266
	mov QWORD PTR [rcx+168], rax
	movabs rax, 55834574860
	mov QWORD PTR [rcx+176], rax
	movabs rax, 64424509454
	mov QWORD PTR [rcx+184], rax
	cmp rdx, 1024
	jb 20f
22:
	vpbroadcastd zmm12, DWORD PTR [rdi+48]
	vpbroadcastd zmm13, DWORD PTR [rdi+52]
	vpbroadcastd zmm14, DWORD PTR [rdi+56]
	vpbroadcastd zmm15, DWORD PTR [rdi+60]
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+128]
	vpaddd zmm12, zmm12, zmm0
	vpbroadcastd zmm0, DWORD PTR [rdi]
	vpbroadcastd zmm1, DWORD PTR [rdi+4]
	vpbroadcastd zmm2, DWORD PTR [rdi+8]
	vpbroadcastd zmm3, DWORD PTR [rdi+12]
	vpbroadcastd zmm4, DWORD PTR [rdi+16]
	vpbroadcastd zmm5, DWORD PTR [rdi+20]
	vpbroadcastd zmm6, DWORD PTR [rdi+24]
	vpbroadcastd zmm7, DWORD PTR [rdi+28]
	vpbroadcastd zmm8, DWORD PTR [rdi+32]
	vpbroadcastd zmm9, DWORD PTR [rdi+36]
	vpbroadcastd zmm10, DWORD PTR [rdi+40]
	vpbroadcastd zmm11, DWORD PTR [rdi+44]
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vmovdqu32 ZMMWORD PTR [rcx], zmm14
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm15
	vpaddd zmm0, zmm0, DWORD PTR [rdi]{1to16}
	vpaddd zmm1, zmm1, DWORD PTR [rdi+4]{1to16}
	vpaddd zmm2, zmm2, DWORD PTR [rdi+8]{1to16}
	vpaddd zmm3, zmm3, DWORD PTR [rdi+12]{1to16}
	vpunpckldq zmm14, zmm0, zmm1
	vpunpckhdq zmm1, zmm0, zmm1
	vpunpckldq zmm15, zmm2, zmm3
	vpunpckhdq zmm3, zmm2, zmm3
	vpunpcklqdq zmm0, zmm14, zmm15
	vpunpckhqdq zmm14, zmm14, zmm15
	vpunpcklqdq zmm2, zmm1, zmm3
	vpunpckhqdq zmm3, zmm1, zmm3
	vpaddd zmm4, zmm4, DWORD PTR [rdi+16]{1to16}
	vpaddd zmm5, zmm5, DWORD PTR [rdi+20]{1to16}
	vpaddd zmm6, zmm6, DWORD PTR [rdi+24]{1to16}
	vpaddd zmm7, zmm7, DWORD PTR [rdi+28]{1to16}
	vpunpckldq zmm1, zmm4, zmm5
	vpunpckhdq zmm5, zmm4, zmm5
	vpunpckldq zmm15, zmm6, zmm7
	vpunpckhdq zmm7, zmm6, zmm7
	vpunpcklqdq zmm4, zmm1, zmm15
	vpunpckhqdq zmm1, zmm1, zmm15
	vpunpcklqdq zmm6, zmm5, zmm7
	vpunpckhqdq zmm7, zmm5, zmm7
	vpaddd zmm8, zmm8, DWORD PTR [rdi+32]{1to16}
	vpaddd zmm9, zmm9, DWORD PTR [rdi+36]{1to16}
	vpaddd zmm10, zmm10, DWORD PTR [rdi+40]{1to16}
	vpaddd zmm11, zmm11, DWORD PTR [rdi+44]{1to16}
	vpunpckldq zmm5, zmm8, zmm9
	vpunpckhdq zmm9, zmm8, zmm9
	vpunpckldq zmm15, zmm10, zmm11
	vpunpckhdq zmm11, zmm10, zmm11
	vpunpcklqdq zmm8, zmm5, zmm15
	vpunpckhqdq zmm5, zmm5, zmm15
	vpunpcklqdq zmm10, zmm9, zmm11
	vpunpckhqdq zmm11, zmm9, zmm11
	vmovdqu32 zmm9, ZMMWORD PTR [rcx]
	vmovdqu32 zmm15, ZMMWORD PTR [rcx+64]
	vmovdqu32 ZMMWORD PTR [rcx], zmm2
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm3
	vpaddd zmm12, zmm12, DWORD PTR [rdi+48]{1to16}
	vpaddd zmm13, zmm13, DWORD PTR [rdi+52]{1to16}
	vpaddd zmm9, zmm9, DWORD PTR [rdi+56]{1to16}
	vpaddd zmm15, zmm15, DWORD PTR [rdi+60]{1to16}
	vmovdqu32 zmm3, ZMMWORD PTR [rcx+128]
	vpaddd zmm12, zmm12, zmm3
	vpunpckldq zmm2, zmm12, zmm13
	vpunpckhdq zmm13, zmm12, zmm13
	vpunpckldq zmm3, zmm9, zmm15
	vpunpckhdq zmm15, zmm9, zmm15
	vpunpcklqdq zmm12, zmm2, zmm3
	vpunpckhqdq zmm2, zmm2, zmm3
	vpunpcklqdq zmm9, zmm13, zmm15
	vpunpckhqdq zmm15, zmm13, zmm15
	vshufi32x4 zmm13, zmm0, zmm4, 68
	vshufi32x4 zmm0, zmm0, zmm4, 238
	vshufi32x4 zmm3, zmm8, zmm12, 68
	vshufi32x4 zmm8, zmm8, zmm12, 238
	vshufi32x4 zmm4, zmm13, zmm3, 136
	vshufi32x4 zmm12, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm0, zmm8, 136
	vshufi32x4 zmm3, zmm0, zmm8, 221
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+256]
	vpxord zmm0, zmm0, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+512]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+768]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+768], zmm0
	vshufi32x4 zmm13, zmm14, zmm1, 68
	vshufi32x4 zmm14, zmm14, zmm1, 238
	vshufi32x4 zmm3, zmm5, zmm2, 68
	vshufi32x4 zmm5, zmm5, zmm2, 238
	vshufi32x4 zmm1, zmm13, zmm3, 136
	vshufi32x4 zmm2, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm14, zmm5, 136
	vshufi32x4 zmm3, zmm14, zmm5, 221
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+64]
	vpxord zmm14, zmm14, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm14
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+320]
	vpxord zmm14, zmm14, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm14
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+576]
	vpxord zmm14, zmm14, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+576], zmm14
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+832]
	vpxord zmm14, zmm14, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+832], zmm14
	vmovdqu32 zmm0, ZMMWORD PTR [rcx]
	vshufi32x4 zmm13, zmm0, zmm6, 68
	vshufi32x4 zmm0, zmm0, zmm6, 238
	vshufi32x4 zmm3, zmm10, zmm9, 68
	vshufi32x4 zmm10, zmm10, zmm9, 238
	vshufi32x4 zmm6, zmm13, zmm3, 136
	vshufi32x4 zmm9, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm0, zmm10, 136
	vshufi32x4 zmm3, zmm0, zmm10, 221
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+128]
	vpxord zmm0, zmm0, zmm6
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+384]
	vpxord zmm0, zmm0, zmm9
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+640]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+640], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+896]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+896], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+64]
	vshufi32x4 zmm13, zmm0, zmm7, 68
	vshufi32x4 zmm0, zmm0, zmm7, 238
	vshufi32x4 zmm3, zmm11, zmm15, 68
	vshufi32x4 zmm11, zmm11, zmm15, 238
	vshufi32x4 zmm7, zmm13, zmm3, 136
	vshufi32x4 zmm15, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm0, zmm11, 136
	vshufi32x4 zmm3, zmm0, zmm11, 221
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+192]
	vpxord zmm0, zmm0, zmm7
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+448]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+704]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+704], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+960]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+960], zmm0
	mov eax, DWORD PTR [rdi+48]
	add eax, 16
	mov DWORD PTR [rdi+48], eax
	add rsi, 1024
	sub rdx, 1024
	cmp rdx, 1024
	jae 22b
	jmp 21f
20:
21:
	cmp rdx, 513
	jb 23f
	cmp rdx, 769
	jb 25f
	mov r9, rcx
	vpbroadcastd zmm12, DWORD PTR [rdi+48]
	vpbroadcastd zmm13, DWORD PTR [rdi+52]
	vpbroadcastd zmm14, DWORD PTR [rdi+56]
	vpbroadcastd zmm15, DWORD PTR [rdi+60]
	vmovdqu32 zmm0, ZMMWORD PTR [r9+128]
	vpaddd zmm12, zmm12, zmm0
	vpbroadcastd zmm0, DWORD PTR [rdi]
	vpbroadcastd zmm1, DWORD PTR [rdi+4]
	vpbroadcastd zmm2, DWORD PTR [rdi+8]
	vpbroadcastd zmm3, DWORD PTR [rdi+12]
	vpbroadcastd zmm4, DWORD PTR [rdi+16]
	vpbroadcastd zmm5, DWORD PTR [rdi+20]
	vpbroadcastd zmm6, DWORD PTR [rdi+24]
	vpbroadcastd zmm7, DWORD PTR [rdi+28]
	vpbroadcastd zmm8, DWORD PTR [rdi+32]
	vpbroadcastd zmm9, DWORD PTR [rdi+36]
	vpbroadcastd zmm10, DWORD PTR [rdi+40]
	vpbroadcastd zmm11, DWORD PTR [rdi+44]
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vmovdqu32 ZMMWORD PTR [r9], zmm14
	vmovdqu32 ZMMWORD PTR [r9+64], zmm15
	vpaddd zmm0, zmm0, DWORD PTR [rdi]{1to16}
	vpaddd zmm1, zmm1, DWORD PTR [rdi+4]{1to16}
	vpaddd zmm2, zmm2, DWORD PTR [rdi+8]{1to16}
	vpaddd zmm3, zmm3, DWORD PTR [rdi+12]{1to16}
	vpunpckldq zmm14, zmm0, zmm1
	vpunpckhdq zmm1, zmm0, zmm1
	vpunpckldq zmm15, zmm2, zmm3
	vpunpckhdq zmm3, zmm2, zmm3
	vpunpcklqdq zmm0, zmm14, zmm15
	vpunpckhqdq zmm14, zmm14, zmm15
	vpunpcklqdq zmm2, zmm1, zmm3
	vpunpckhqdq zmm3, zmm1, zmm3
	vpaddd zmm4, zmm4, DWORD PTR [rdi+16]{1to16}
	vpaddd zmm5, zmm5, DWORD PTR [rdi+20]{1to16}
	vpaddd zmm6, zmm6, DWORD PTR [rdi+24]{1to16}
	vpaddd zmm7, zmm7, DWORD PTR [rdi+28]{1to16}
	vpunpckldq zmm1, zmm4, zmm5
	vpunpckhdq zmm5, zmm4, zmm5
	vpunpckldq zmm15, zmm6, zmm7
	vpunpckhdq zmm7, zmm6, zmm7
	vpunpcklqdq zmm4, zmm1, zmm15
	vpunpckhqdq zmm1, zmm1, zmm15
	vpunpcklqdq zmm6, zmm5, zmm7
	vpunpckhqdq zmm7, zmm5, zmm7
	vpaddd zmm8, zmm8, DWORD PTR [rdi+32]{1to16}
	vpaddd zmm9, zmm9, DWORD PTR [rdi+36]{1to16}
	vpaddd zmm10, zmm10, DWORD PTR [rdi+40]{1to16}
	vpaddd zmm11, zmm11, DWORD PTR [rdi+44]{1to16}
	vpunpckldq zmm5, zmm8, zmm9
	vpunpckhdq zmm9, zmm8, zmm9
	vpunpckldq zmm15, zmm10, zmm11
	vpunpckhdq zmm11, zmm10, zmm11
	vpunpcklqdq zmm8, zmm5, zmm15
	vpunpckhqdq zmm5, zmm5, zmm15
	vpunpcklqdq zmm10, zmm9, zmm11
	vpunpckhqdq zmm11, zmm9, zmm11
	vmovdqu32 zmm9, ZMMWORD PTR [r9]
	vmovdqu32 zmm15, ZMMWORD PTR [r9+64]
	vmovdqu32 ZMMWORD PTR [r9], zmm2
	vmovdqu32 ZMMWORD PTR [r9+64], zmm3
	vpaddd zmm12, zmm12, DWORD PTR [rdi+48]{1to16}
	vpaddd zmm13, zmm13, DWORD PTR [rdi+52]{1to16}
	vpaddd zmm9, zmm9, DWORD PTR [rdi+56]{1to16}
	vpaddd zmm15, zmm15, DWORD PTR [rdi+60]{1to16}
	vmovdqu32 zmm3, ZMMWORD PTR [r9+128]
	vpaddd zmm12, zmm12, zmm3
	vpunpckldq zmm2, zmm12, zmm13
	vpunpckhdq zmm13, zmm12, zmm13
	vpunpckldq zmm3, zmm9, zmm15
	vpunpckhdq zmm15, zmm9, zmm15
	vpunpcklqdq zmm12, zmm2, zmm3
	vpunpckhqdq zmm2, zmm2, zmm3
	vpunpcklqdq zmm9, zmm13, zmm15
	vpunpckhqdq zmm15, zmm13, zmm15
	vshufi32x4 zmm13, zmm0, zmm4, 68
	vshufi32x4 zmm0, zmm0, zmm4, 238
	vshufi32x4 zmm3, zmm8, zmm12, 68
	vshufi32x4 zmm8, zmm8, zmm12, 238
	vshufi32x4 zmm4, zmm13, zmm3, 136
	vshufi32x4 zmm12, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm0, zmm8, 136
	vshufi32x4 zmm3, zmm0, zmm8, 221
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+256]
	vpxord zmm0, zmm0, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm0
	vshufi32x4 zmm0, zmm14, zmm1, 68
	vshufi32x4 zmm14, zmm14, zmm1, 238
	vshufi32x4 zmm8, zmm5, zmm2, 68
	vshufi32x4 zmm5, zmm5, zmm2, 238
	vshufi32x4 zmm1, zmm0, zmm8, 136
	vshufi32x4 zmm2, zmm0, zmm8, 221
	vshufi32x4 zmm0, zmm14, zmm5, 136
	vshufi32x4 zmm8, zmm14, zmm5, 221
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+64]
	vpxord zmm14, zmm14, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm14
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+320]
	vpxord zmm14, zmm14, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm14
	vmovdqu32 zmm4, ZMMWORD PTR [r9]
	vshufi32x4 zmm12, zmm4, zmm6, 68
	vshufi32x4 zmm4, zmm4, zmm6, 238
	vshufi32x4 zmm14, zmm10, zmm9, 68
	vshufi32x4 zmm10, zmm10, zmm9, 238
	vshufi32x4 zmm6, zmm12, zmm14, 136
	vshufi32x4 zmm9, zmm12, zmm14, 221
	vshufi32x4 zmm12, zmm4, zmm10, 136
	vshufi32x4 zmm14, zmm4, zmm10, 221
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+128]
	vpxord zmm4, zmm4, zmm6
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm4
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+384]
	vpxord zmm4, zmm4, zmm9
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm4
	vmovdqu32 zmm4, ZMMWORD PTR [r9+64]
	vshufi32x4 zmm5, zmm4, zmm7, 68
	vshufi32x4 zmm4, zmm4, zmm7, 238
	vshufi32x4 zmm1, zmm11, zmm15, 68
	vshufi32x4 zmm11, zmm11, zmm15, 238
	vshufi32x4 zmm7, zmm5, zmm1, 136
	vshufi32x4 zmm15, zmm5, zmm1, 221
	vshufi32x4 zmm5, zmm4, zmm11, 136
	vshufi32x4 zmm1, zmm4, zmm11, 221
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+192]
	vpxord zmm4, zmm4, zmm7
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm4
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+448]
	vpxord zmm4, zmm4, zmm15
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm4
	add rsi, 512
	sub rdx, 512
	cmp rdx, 512
	jb 27f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+448]
	vpxord zmm2, zmm2, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm2
	jmp 28f
27:
	vmovdqu32 ZMMWORD PTR [r9], zmm1
28:
	cmp rdx, 448
	jb 29f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+384]
	vpxord zmm2, zmm2, zmm14
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm2
	jmp 210f
29:
	vmovdqu32 ZMMWORD PTR [r9], zmm14
210:
	cmp rdx, 384
	jb 211f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+320]
	vpxord zmm2, zmm2, zmm8
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm2
	jmp 212f
211:
	vmovdqu32 ZMMWORD PTR [r9], zmm8
212:
	cmp rdx, 320
	jb 213f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+256]
	vpxord zmm2, zmm2, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm2
	jmp 214f
213:
	vmovdqu32 ZMMWORD PTR [r9], zmm3
214:
	cmp rdx, 256
	jb 215f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+192]
	vpxord zmm2, zmm2, zmm5
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm2
	jmp 216f
215:
	vmovdqu32 ZMMWORD PTR [r9], zmm5
216:
	cmp rdx, 192
	jb 217f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+128]
	vpxord zmm2, zmm2, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm2
	jmp 218f
217:
	vmovdqu32 ZMMWORD PTR [r9], zmm12
218:
	cmp rdx, 128
	jb 219f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+64]
	vpxord zmm2, zmm2, zmm0
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm2
	jmp 220f
219:
	vmovdqu32 ZMMWORD PTR [r9], zmm0
220:
	cmp rdx, 64
	jb 221f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi]
	vpxord zmm2, zmm2, zmm13
	vmovdqu32 ZMMWORD PTR [rsi], zmm2
	jmp 222f
221:
	vmovdqu32 ZMMWORD PTR [r9], zmm13
222:
	mov rax, rdx
	shr rax, 6
	shl rax, 6
	add rsi, rax
	sub rdx, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 223f
225:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
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
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 228b
	jmp 227f
226:
227:
	vzeroupper
	mov rsi, r9
	jmp 26f
25:
	mov r9, rcx
	movabs rax, 8
	mov QWORD PTR [rcx], rax
	movabs rax, 0
	mov QWORD PTR [rcx+8], rax
	movabs rax, 9
	mov QWORD PTR [rcx+16], rax
	movabs rax, 0
	mov QWORD PTR [rcx+24], rax
	movabs rax, 10
	mov QWORD PTR [rcx+32], rax
	movabs rax, 0
	mov QWORD PTR [rcx+40], rax
	movabs rax, 11
	mov QWORD PTR [rcx+48], rax
	movabs rax, 0
	mov QWORD PTR [rcx+56], rax
	vbroadcasti32x4 zmm0, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm1, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm2, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm3, XMMWORD PTR [rdi+48]
	vporq zmm4, zmm0, zmm0
	vporq zmm5, zmm1, zmm1
	vporq zmm6, zmm2, zmm2
	vporq zmm8, zmm0, zmm0
	vporq zmm9, zmm1, zmm1
	vporq zmm10, zmm2, zmm2
	vmovdqu32 zmm12, ZMMWORD PTR [r9+256]
	vmovdqu32 zmm13, ZMMWORD PTR [r9+192]
	vmovdqu32 zmm14, ZMMWORD PTR [r9]
	vpaddd zmm7, zmm3, zmm13
	vpaddd zmm11, zmm3, zmm14
	vpaddd zmm3, zmm3, zmm12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpshufd zmm9, zmm9, 57
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vprold zmm11, zmm11, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vprold zmm9, zmm9, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpaddd zmm8, zmm8, zmm9
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vpxord zmm11, zmm11, zmm8
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vprold zmm11, zmm11, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpaddd zmm10, zmm10, zmm11
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vpxord zmm9, zmm9, zmm10
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vprold zmm9, zmm9, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpshufd zmm9, zmm9, 147
	vpshufd zmm10, zmm10, 78
	vpshufd zmm11, zmm11, 57
	vbroadcasti32x4 zmm12, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm14, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm15, XMMWORD PTR [rdi+48]
	vpaddd zmm0, zmm0, zmm12
	vpaddd zmm1, zmm1, zmm13
	vpaddd zmm2, zmm2, zmm14
	vpaddd zmm4, zmm4, zmm12
	vpaddd zmm5, zmm5, zmm13
	vpaddd zmm6, zmm6, zmm14
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vmovdqu32 zmm12, ZMMWORD PTR [r9+256]
	vpaddd zmm12, zmm12, zmm15
	vpaddd zmm3, zmm3, zmm12
	vmovdqu32 zmm13, ZMMWORD PTR [r9+192]
	vpaddd zmm13, zmm13, zmm15
	vpaddd zmm7, zmm7, zmm13
	vmovdqu32 zmm14, ZMMWORD PTR [r9]
	vpaddd zmm14, zmm14, zmm15
	vpaddd zmm11, zmm11, zmm14
	vshufi32x4 zmm12, zmm0, zmm1, 68
	vshufi32x4 zmm13, zmm2, zmm3, 68
	vshufi32x4 zmm14, zmm0, zmm1, 238
	vshufi32x4 zmm15, zmm2, zmm3, 238
	vshufi32x4 zmm0, zmm12, zmm13, 136
	vshufi32x4 zmm1, zmm12, zmm13, 221
	vshufi32x4 zmm2, zmm14, zmm15, 136
	vshufi32x4 zmm3, zmm14, zmm15, 221
	vmovdqu32 zmm12, ZMMWORD PTR [rsi]
	vpxord zmm12, zmm12, zmm0
	vmovdqu32 ZMMWORD PTR [rsi], zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rsi+64]
	vpxord zmm12, zmm12, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rsi+128]
	vpxord zmm12, zmm12, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rsi+192]
	vpxord zmm12, zmm12, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm12
	vshufi32x4 zmm12, zmm4, zmm5, 68
	vshufi32x4 zmm13, zmm6, zmm7, 68
	vshufi32x4 zmm14, zmm4, zmm5, 238
	vshufi32x4 zmm15, zmm6, zmm7, 238
	vshufi32x4 zmm4, zmm12, zmm13, 136
	vshufi32x4 zmm5, zmm12, zmm13, 221
	vshufi32x4 zmm6, zmm14, zmm15, 136
	vshufi32x4 zmm7, zmm14, zmm15, 221
	vmovdqu32 zmm12, ZMMWORD PTR [rsi+256]
	vpxord zmm12, zmm12, zmm4
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rsi+320]
	vpxord zmm12, zmm12, zmm5
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rsi+384]
	vpxord zmm12, zmm12, zmm6
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rsi+448]
	vpxord zmm12, zmm12, zmm7
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm12
	vshufi32x4 zmm12, zmm8, zmm9, 68
	vshufi32x4 zmm13, zmm10, zmm11, 68
	vshufi32x4 zmm14, zmm8, zmm9, 238
	vshufi32x4 zmm15, zmm10, zmm11, 238
	vshufi32x4 zmm8, zmm12, zmm13, 136
	vshufi32x4 zmm9, zmm12, zmm13, 221
	vshufi32x4 zmm10, zmm14, zmm15, 136
	vshufi32x4 zmm11, zmm14, zmm15, 221
	vmovdqu32 ZMMWORD PTR [r9], zmm8
	vmovdqu32 ZMMWORD PTR [r9+64], zmm9
	vmovdqu32 ZMMWORD PTR [r9+128], zmm10
	vmovdqu32 ZMMWORD PTR [r9+192], zmm11
	add rsi, 512
	sub rdx, 512
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 229f
231:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 231b
	jmp 230f
229:
230:
	cmp rcx, rdx
	je 232f
234:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 234b
	jmp 233f
232:
233:
	vzeroupper
	mov rsi, r9
26:
	jmp 24f
23:
	mov r9, rcx
	cmp rdx, 512
	jb 235f
	vbroadcasti32x4 zmm0, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm1, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm2, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm3, XMMWORD PTR [rdi+48]
	vporq zmm4, zmm0, zmm0
	vporq zmm5, zmm1, zmm1
	vporq zmm6, zmm2, zmm2
	vmovdqu32 zmm8, ZMMWORD PTR [r9+256]
	vmovdqu32 zmm9, ZMMWORD PTR [r9+192]
	vpaddd zmm7, zmm3, zmm9
	vpaddd zmm3, zmm3, zmm8
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm9, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm10, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm11, XMMWORD PTR [rdi+48]
	vpaddd zmm0, zmm0, zmm8
	vpaddd zmm1, zmm1, zmm9
	vpaddd zmm2, zmm2, zmm10
	vpaddd zmm4, zmm4, zmm8
	vpaddd zmm5, zmm5, zmm9
	vpaddd zmm6, zmm6, zmm10
	vmovdqu32 zmm12, ZMMWORD PTR [r9+256]
	vpaddd zmm12, zmm12, zmm11
	vpaddd zmm3, zmm3, zmm12
	vmovdqu32 zmm13, ZMMWORD PTR [r9+192]
	vpaddd zmm13, zmm13, zmm11
	vpaddd zmm7, zmm7, zmm13
	vshufi32x4 zmm8, zmm0, zmm1, 68
	vshufi32x4 zmm9, zmm2, zmm3, 68
	vshufi32x4 zmm10, zmm0, zmm1, 238
	vshufi32x4 zmm11, zmm2, zmm3, 238
	vshufi32x4 zmm0, zmm8, zmm9, 136
	vshufi32x4 zmm1, zmm8, zmm9, 221
	vshufi32x4 zmm2, zmm10, zmm11, 136
	vshufi32x4 zmm3, zmm10, zmm11, 221
	vshufi32x4 zmm8, zmm4, zmm5, 68
	vshufi32x4 zmm9, zmm6, zmm7, 68
	vshufi32x4 zmm10, zmm4, zmm5, 238
	vshufi32x4 zmm11, zmm6, zmm7, 238
	vshufi32x4 zmm4, zmm8, zmm9, 136
	vshufi32x4 zmm5, zmm8, zmm9, 221
	vshufi32x4 zmm6, zmm10, zmm11, 136
	vshufi32x4 zmm7, zmm10, zmm11, 221
	vmovdqu32 zmm8, ZMMWORD PTR [rsi]
	vpxord zmm8, zmm8, zmm0
	vmovdqu32 ZMMWORD PTR [rsi], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+64]
	vpxord zmm8, zmm8, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+128]
	vpxord zmm8, zmm8, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+192]
	vpxord zmm8, zmm8, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+256]
	vpxord zmm8, zmm8, zmm4
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+320]
	vpxord zmm8, zmm8, zmm5
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+384]
	vpxord zmm8, zmm8, zmm6
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+448]
	vpxord zmm8, zmm8, zmm7
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm8
	mov eax, DWORD PTR [rdi+48]
	add eax, 8
	mov DWORD PTR [rdi+48], eax
	add rsi, 512
	sub rdx, 512
	jmp 236f
235:
236:
	cmp rdx, 257
	jb 237f
	vbroadcasti32x4 zmm0, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm1, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm2, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm3, XMMWORD PTR [rdi+48]
	vporq zmm4, zmm0, zmm0
	vporq zmm5, zmm1, zmm1
	vporq zmm6, zmm2, zmm2
	vmovdqu32 zmm8, ZMMWORD PTR [r9+256]
	vmovdqu32 zmm9, ZMMWORD PTR [r9+192]
	vpaddd zmm7, zmm3, zmm9
	vpaddd zmm3, zmm3, zmm8
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpshufd zmm5, zmm5, 57
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 147
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 16
	vprold zmm7, zmm7, 16
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 12
	vprold zmm5, zmm5, 12
	vpaddd zmm0, zmm0, zmm1
	vpaddd zmm4, zmm4, zmm5
	vpxord zmm3, zmm3, zmm0
	vpxord zmm7, zmm7, zmm4
	vprold zmm3, zmm3, 8
	vprold zmm7, zmm7, 8
	vpaddd zmm2, zmm2, zmm3
	vpaddd zmm6, zmm6, zmm7
	vpxord zmm1, zmm1, zmm2
	vpxord zmm5, zmm5, zmm6
	vprold zmm1, zmm1, 7
	vprold zmm5, zmm5, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpshufd zmm5, zmm5, 147
	vpshufd zmm6, zmm6, 78
	vpshufd zmm7, zmm7, 57
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm9, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm10, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm11, XMMWORD PTR [rdi+48]
	vpaddd zmm0, zmm0, zmm8
	vpaddd zmm1, zmm1, zmm9
	vpaddd zmm2, zmm2, zmm10
	vpaddd zmm4, zmm4, zmm8
	vpaddd zmm5, zmm5, zmm9
	vpaddd zmm6, zmm6, zmm10
	vmovdqu32 zmm12, ZMMWORD PTR [r9+256]
	vpaddd zmm12, zmm12, zmm11
	vpaddd zmm3, zmm3, zmm12
	vmovdqu32 zmm13, ZMMWORD PTR [r9+192]
	vpaddd zmm13, zmm13, zmm11
	vpaddd zmm7, zmm7, zmm13
	vshufi32x4 zmm8, zmm0, zmm1, 68
	vshufi32x4 zmm9, zmm2, zmm3, 68
	vshufi32x4 zmm10, zmm0, zmm1, 238
	vshufi32x4 zmm11, zmm2, zmm3, 238
	vshufi32x4 zmm0, zmm8, zmm9, 136
	vshufi32x4 zmm1, zmm8, zmm9, 221
	vshufi32x4 zmm2, zmm10, zmm11, 136
	vshufi32x4 zmm3, zmm10, zmm11, 221
	vshufi32x4 zmm8, zmm4, zmm5, 68
	vshufi32x4 zmm9, zmm6, zmm7, 68
	vshufi32x4 zmm10, zmm4, zmm5, 238
	vshufi32x4 zmm11, zmm6, zmm7, 238
	vshufi32x4 zmm4, zmm8, zmm9, 136
	vshufi32x4 zmm5, zmm8, zmm9, 221
	vshufi32x4 zmm6, zmm10, zmm11, 136
	vshufi32x4 zmm7, zmm10, zmm11, 221
	vmovdqu32 zmm8, ZMMWORD PTR [rsi]
	vpxord zmm8, zmm8, zmm0
	vmovdqu32 ZMMWORD PTR [rsi], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+64]
	vpxord zmm8, zmm8, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+128]
	vpxord zmm8, zmm8, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm8
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+192]
	vpxord zmm8, zmm8, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm8
	vmovdqu32 ZMMWORD PTR [r9], zmm4
	vmovdqu32 ZMMWORD PTR [r9+64], zmm5
	vmovdqu32 ZMMWORD PTR [r9+128], zmm6
	vmovdqu32 ZMMWORD PTR [r9+192], zmm7
	add rsi, 256
	sub rdx, 256
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 239f
241:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 241b
	jmp 240f
239:
240:
	cmp rcx, rdx
	je 242f
244:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 244b
	jmp 243f
242:
243:
	jmp 238f
237:
	test rdx, rdx
	je 245f
	vbroadcasti32x4 zmm0, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm1, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm2, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm3, XMMWORD PTR [rdi+48]
	vmovdqu32 zmm4, ZMMWORD PTR [r9+256]
	vpaddd zmm3, zmm3, zmm4
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 57
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 147
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 16
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 12
	vpaddd zmm0, zmm0, zmm1
	vpxord zmm3, zmm3, zmm0
	vprold zmm3, zmm3, 8
	vpaddd zmm2, zmm2, zmm3
	vpxord zmm1, zmm1, zmm2
	vprold zmm1, zmm1, 7
	vpshufd zmm1, zmm1, 147
	vpshufd zmm2, zmm2, 78
	vpshufd zmm3, zmm3, 57
	vbroadcasti32x4 zmm4, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm5, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm6, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm7, XMMWORD PTR [rdi+48]
	vmovdqu32 zmm8, ZMMWORD PTR [r9+256]
	vpaddd zmm7, zmm7, zmm8
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vshufi32x4 zmm4, zmm0, zmm1, 68
	vshufi32x4 zmm5, zmm2, zmm3, 68
	vshufi32x4 zmm6, zmm0, zmm1, 238
	vshufi32x4 zmm7, zmm2, zmm3, 238
	vshufi32x4 zmm0, zmm4, zmm5, 136
	vshufi32x4 zmm1, zmm4, zmm5, 221
	vshufi32x4 zmm2, zmm6, zmm7, 136
	vshufi32x4 zmm3, zmm6, zmm7, 221
	vmovdqu32 ZMMWORD PTR [r9], zmm0
	vmovdqu32 ZMMWORD PTR [r9+64], zmm1
	vmovdqu32 ZMMWORD PTR [r9+128], zmm2
	vmovdqu32 ZMMWORD PTR [r9+192], zmm3
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 247f
249:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 249b
	jmp 248f
247:
248:
	cmp rcx, rdx
	je 250f
252:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 252b
	jmp 251f
250:
251:
	jmp 246f
245:
246:
238:
	vzeroupper
	mov rsi, r9
24:
	ret
	.p2align 6
