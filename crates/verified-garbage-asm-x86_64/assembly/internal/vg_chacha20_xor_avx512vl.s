// The functions of `src/internal/vg_chacha20_xor_avx512vl.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor_avx512vl:
	cmp rdx, 513
	jb 20f
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
	jb 22f
24:
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
	jae 24b
	jmp 23f
22:
23:
	cmp rdx, 513
	jb 25f
	cmp rdx, 769
	jb 27f
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
	jb 29f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+448]
	vpxord zmm2, zmm2, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm2
	jmp 210f
29:
	vmovdqu32 ZMMWORD PTR [r9], zmm1
210:
	cmp rdx, 448
	jb 211f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+384]
	vpxord zmm2, zmm2, zmm14
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm2
	jmp 212f
211:
	vmovdqu32 ZMMWORD PTR [r9], zmm14
212:
	cmp rdx, 384
	jb 213f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+320]
	vpxord zmm2, zmm2, zmm8
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm2
	jmp 214f
213:
	vmovdqu32 ZMMWORD PTR [r9], zmm8
214:
	cmp rdx, 320
	jb 215f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+256]
	vpxord zmm2, zmm2, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm2
	jmp 216f
215:
	vmovdqu32 ZMMWORD PTR [r9], zmm3
216:
	cmp rdx, 256
	jb 217f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+192]
	vpxord zmm2, zmm2, zmm5
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm2
	jmp 218f
217:
	vmovdqu32 ZMMWORD PTR [r9], zmm5
218:
	cmp rdx, 192
	jb 219f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+128]
	vpxord zmm2, zmm2, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm2
	jmp 220f
219:
	vmovdqu32 ZMMWORD PTR [r9], zmm12
220:
	cmp rdx, 128
	jb 221f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+64]
	vpxord zmm2, zmm2, zmm0
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm2
	jmp 222f
221:
	vmovdqu32 ZMMWORD PTR [r9], zmm0
222:
	cmp rdx, 64
	jb 223f
	vmovdqu32 zmm2, ZMMWORD PTR [rsi]
	vpxord zmm2, zmm2, zmm13
	vmovdqu32 ZMMWORD PTR [rsi], zmm2
	jmp 224f
223:
	vmovdqu32 ZMMWORD PTR [r9], zmm13
224:
	mov rax, rdx
	shr rax, 6
	shl rax, 6
	add rsi, rax
	sub rdx, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 225f
227:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 227b
	jmp 226f
225:
226:
	cmp rcx, rdx
	je 228f
230:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 230b
	jmp 229f
228:
229:
	vzeroupper
	mov rsi, r9
	jmp 28f
27:
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
	je 231f
233:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
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
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 236b
	jmp 235f
234:
235:
	vzeroupper
	mov rsi, r9
28:
	jmp 26f
25:
	mov r9, rcx
	cmp rdx, 512
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
	jmp 238f
237:
238:
	cmp rdx, 257
	jb 239f
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
	je 241f
243:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 243b
	jmp 242f
241:
242:
	cmp rcx, rdx
	je 244f
246:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 246b
	jmp 245f
244:
245:
	jmp 240f
239:
	test rdx, rdx
	je 247f
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
	je 249f
251:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 251b
	jmp 250f
249:
250:
	cmp rcx, rdx
	je 252f
254:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 254b
	jmp 253f
252:
253:
	jmp 248f
247:
248:
240:
	vzeroupper
	mov rsi, r9
26:
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
	cmp rdx, 512
	jb 255f
257:
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
	jae 257b
	jmp 256f
255:
256:
	cmp rdx, 385
	jb 258f
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
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 260f
262:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 262b
	jmp 261f
260:
261:
	cmp rcx, rdx
	je 263f
265:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 265b
	jmp 264f
263:
264:
	vzeroupper
	mov rsi, r9
	jmp 259f
258:
	mov r9, rcx
	cmp rdx, 257
	jb 266f
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
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 268f
270:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 270b
	jmp 269f
268:
269:
	cmp rcx, rdx
	je 271f
273:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 273b
	jmp 272f
271:
272:
	jmp 267f
266:
	cmp rdx, 129
	jb 274f
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
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 276f
278:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 278b
	jmp 277f
276:
277:
	cmp rcx, rdx
	je 279f
281:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 281b
	jmp 280f
279:
280:
	jmp 275f
274:
	test rdx, rdx
	je 282f
	cmp rdx, 65
	jb 284f
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
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 286f
288:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 288b
	jmp 287f
286:
287:
	cmp rcx, rdx
	je 289f
291:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 291b
	jmp 290f
289:
290:
	jmp 285f
284:
	vzeroupper
	call {vg_chacha20_xor}
	mov r9, rsi
285:
	jmp 283f
282:
283:
275:
267:
	vzeroupper
	mov rsi, r9
259:
21:
	ret
	.p2align 6
