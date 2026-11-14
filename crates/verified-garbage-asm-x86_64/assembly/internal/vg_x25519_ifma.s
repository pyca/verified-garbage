// The functions of `src/internal/vg_x25519_ifma.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519_ifma:
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	movabs rax, 9223372036854775807
	and r11, rax
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov QWORD PTR [rcx+24], r13
	mov QWORD PTR [rcx+32], r14
	mov QWORD PTR [rcx+40], r15
	mov r12, rdi
	mov rdi, rcx
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	mov eax, 0
	mov edx, 1
	mov QWORD PTR [rdi+96], rdx
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+192], rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+640], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rsi+rbx*1]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+768], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+769], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+770], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+771], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+772], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+773], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+774], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+775], dl
	add rbx, 1
	cmp rbx, 32
	jne 20b
	mov eax, 0
	mov BYTE PTR [rdi+768], al
	mov BYTE PTR [rdi+769], al
	mov BYTE PTR [rdi+770], al
	mov eax, 1
	mov BYTE PTR [rdi+1022], al
	mov rsi, r12
	movabs rax, 4294967296
	movabs rcx, 8589934594
	movabs rdx, 17179869188
	vmovq xmm5, rax
	vpbroadcastq ymm5, xmm5
	vmovq xmm6, rcx
	vpbroadcastq ymm6, xmm6
	vmovq xmm7, rdx
	vpbroadcastq ymm7, xmm7
	vmovdqu YMMWORD PTR [rdi+1568], ymm7
	vpxor ymm11, ymm11, ymm11
	vpblendd ymm8, ymm11, ymm6, 60
	vpblendd ymm9, ymm11, ymm7, 240
	vpaddq ymm10, ymm5, ymm8
	vpaddq ymm10, ymm10, ymm9
	vmovdqu YMMWORD PTR [rdi+1600], ymm10
	vpblendd ymm8, ymm11, ymm6, 204
	vpaddq ymm10, ymm5, ymm8
	vmovdqu YMMWORD PTR [rdi+1632], ymm10
	movabs rax, 2251799813685247
	mov ecx, 19
	movabs rdx, 4611686018427348992
	movabs rbp, 4611686018427385856
	mov r8d, 8191
	mov r9d, 67108863
	movabs r10, 549755813887
	mov r11d, 1
	mov r12d, 121665
	vmovq xmm9, rax
	vpbroadcastq ymm9, xmm9
	vmovdqu YMMWORD PTR [rdi+1664], ymm9
	vmovq xmm10, rcx
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1696], ymm10
	vmovq xmm10, rdx
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1728], ymm10
	vmovq xmm10, rbp
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1760], ymm10
	vmovq xmm10, r8
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+2112], ymm10
	vmovq xmm10, r9
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+2144], ymm10
	vmovq xmm10, r10
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+2176], ymm10
	vmovq xmm10, r11
	vpermq ymm13, ymm10, 20
	vpermq ymm14, ymm10, 68
	vmovq xmm10, r12
	vpermq ymm15, ymm10, 81
	vpxor ymm12, ymm12, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+64]
	vpermq ymm5, ymm10, 0
	vpermq ymm6, ymm10, 85
	vpermq ymm7, ymm10, 170
	vpermq ymm8, ymm10, 255
	vpand ymm0, ymm5, ymm9
	vpsrlq ymm1, ymm5, 51
	vpsrlq ymm11, ymm9, 13
	vpand ymm11, ymm6, ymm11
	vpsllq ymm11, ymm11, 13
	vpor ymm1, ymm1, ymm11
	vpsrlq ymm2, ymm6, 38
	vpsrlq ymm11, ymm9, 26
	vpand ymm11, ymm7, ymm11
	vpsllq ymm11, ymm11, 26
	vpor ymm2, ymm2, ymm11
	vpsrlq ymm3, ymm7, 25
	vpsrlq ymm11, ymm9, 39
	vpand ymm11, ymm8, ymm11
	vpsllq ymm11, ymm11, 39
	vpor ymm3, ymm3, ymm11
	vpsrlq ymm4, ymm8, 12
	vpblendd ymm11, ymm14, ymm0, 192
	vmovdqu YMMWORD PTR [rdi+1952], ymm11
	vmovdqu YMMWORD PTR [rdi+1792], ymm15
	vpblendd ymm0, ymm13, ymm0, 48
	vpblendd ymm11, ymm12, ymm1, 192
	vmovdqu YMMWORD PTR [rdi+1984], ymm11
	vmovdqu YMMWORD PTR [rdi+1824], ymm12
	vpblendd ymm1, ymm12, ymm1, 48
	vpblendd ymm11, ymm12, ymm2, 192
	vmovdqu YMMWORD PTR [rdi+2016], ymm11
	vmovdqu YMMWORD PTR [rdi+1856], ymm12
	vpblendd ymm2, ymm12, ymm2, 48
	vpblendd ymm11, ymm12, ymm3, 192
	vmovdqu YMMWORD PTR [rdi+2048], ymm11
	vmovdqu YMMWORD PTR [rdi+1888], ymm12
	vpblendd ymm3, ymm12, ymm3, 48
	vpblendd ymm11, ymm12, ymm4, 192
	vmovdqu YMMWORD PTR [rdi+2080], ymm11
	vmovdqu YMMWORD PTR [rdi+1920], ymm12
	vpblendd ymm4, ymm12, ymm4, 48
	stmxcsr DWORD PTR [rdi+2208]
	mov r11d, DWORD PTR [rdi+2208]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rdi+2212], eax
	ldmxcsr DWORD PTR [rdi+2212]
	lfence
	mov ebx, 255
21:
	sub rbx, 1
	movzx eax, BYTE PTR [rdi+rbx*1+768]
	mov rdx, QWORD PTR [rdi+640]
	xor rdx, rax
	mov QWORD PTR [rdi+640], rax
	mov ecx, 0
	sub rcx, rdx
	vmovq xmm15, rcx
	vpbroadcastq ymm15, xmm15
	vpunpcklqdq ymm10, ymm0, ymm0
	vpunpckhqdq ymm11, ymm0, ymm0
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm0, ymm10, ymm11
	vpunpcklqdq ymm10, ymm1, ymm1
	vpunpckhqdq ymm11, ymm1, ymm1
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm1, ymm10, ymm11
	vpunpcklqdq ymm10, ymm2, ymm2
	vpunpckhqdq ymm11, ymm2, ymm2
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm2, ymm10, ymm11
	vpunpcklqdq ymm10, ymm3, ymm3
	vpunpckhqdq ymm11, ymm3, ymm3
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm3, ymm10, ymm11
	vpunpcklqdq ymm10, ymm4, ymm4
	vpunpckhqdq ymm11, ymm4, ymm4
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm4, ymm10, ymm11
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu ymm5, YMMWORD PTR [rdi+1568]
	vpand ymm15, ymm15, ymm5
	vmovdqu ymm5, YMMWORD PTR [rdi+1600]
	vpxor ymm5, ymm15, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdi+1632]
	vpxor ymm15, ymm15, ymm6
	vpermd ymm10, ymm5, ymm0
	vpermd ymm11, ymm5, ymm1
	vpermd ymm12, ymm5, ymm2
	vpermd ymm13, ymm5, ymm3
	vpermd ymm14, ymm5, ymm4
	vpermd ymm5, ymm15, ymm0
	vpermd ymm6, ymm15, ymm1
	vpermd ymm7, ymm15, ymm2
	vpermd ymm8, ymm15, ymm3
	vpermd ymm9, ymm15, ymm4
	vpxor ymm0, ymm0, ymm0
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm17, ymm11, ymm9
	vpmadd52huq ymm18, ymm11, ymm8
	vpmadd52luq ymm17, ymm12, ymm8
	vpmadd52huq ymm18, ymm12, ymm7
	vpmadd52luq ymm17, ymm13, ymm7
	vpmadd52huq ymm18, ymm13, ymm6
	vpmadd52luq ymm17, ymm14, ymm6
	vpmadd52huq ymm18, ymm14, ymm5
	vpmadd52luq ymm0, ymm10, ymm5
	vpmadd52huq ymm18, ymm10, ymm9
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm0, ymm0, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm0, ymm0, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm0, ymm0, ymm18
	vpxor ymm1, ymm1, ymm1
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm1, ymm11, ymm5
	vpmadd52huq ymm18, ymm11, ymm9
	vpmadd52luq ymm17, ymm12, ymm9
	vpmadd52huq ymm18, ymm12, ymm8
	vpmadd52luq ymm17, ymm13, ymm8
	vpmadd52huq ymm18, ymm13, ymm7
	vpmadd52luq ymm17, ymm14, ymm7
	vpmadd52huq ymm18, ymm14, ymm6
	vpmadd52luq ymm1, ymm10, ymm6
	vpmadd52huq ymm16, ymm10, ymm5
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm1, ymm1, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm1, ymm1, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm1, ymm1, ymm18
	vpxor ymm2, ymm2, ymm2
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm2, ymm11, ymm6
	vpmadd52huq ymm16, ymm11, ymm5
	vpmadd52luq ymm2, ymm12, ymm5
	vpmadd52huq ymm18, ymm12, ymm9
	vpmadd52luq ymm17, ymm13, ymm9
	vpmadd52huq ymm18, ymm13, ymm8
	vpmadd52luq ymm17, ymm14, ymm8
	vpmadd52huq ymm18, ymm14, ymm7
	vpmadd52luq ymm2, ymm10, ymm7
	vpmadd52huq ymm16, ymm10, ymm6
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm2, ymm2, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm2, ymm2, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm2, ymm2, ymm18
	vpxor ymm3, ymm3, ymm3
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm3, ymm11, ymm7
	vpmadd52huq ymm16, ymm11, ymm6
	vpmadd52luq ymm3, ymm12, ymm6
	vpmadd52huq ymm16, ymm12, ymm5
	vpmadd52luq ymm3, ymm13, ymm5
	vpmadd52huq ymm18, ymm13, ymm9
	vpmadd52luq ymm17, ymm14, ymm9
	vpmadd52huq ymm18, ymm14, ymm8
	vpmadd52luq ymm3, ymm10, ymm8
	vpmadd52huq ymm16, ymm10, ymm7
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm3, ymm3, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm3, ymm3, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm3, ymm3, ymm18
	vpxor ymm4, ymm4, ymm4
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm4, ymm11, ymm8
	vpmadd52huq ymm16, ymm11, ymm7
	vpmadd52luq ymm4, ymm12, ymm7
	vpmadd52huq ymm16, ymm12, ymm6
	vpmadd52luq ymm4, ymm13, ymm6
	vpmadd52huq ymm16, ymm13, ymm5
	vpmadd52luq ymm4, ymm14, ymm5
	vpmadd52huq ymm18, ymm14, ymm9
	vpmadd52luq ymm4, ymm10, ymm9
	vpmadd52huq ymm16, ymm10, ymm8
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm4, ymm4, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm4, ymm4, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm4, ymm4, ymm18
	vpunpcklqdq ymm15, ymm0, ymm0
	vpunpckhqdq ymm10, ymm0, ymm0
	vmovdqu ymm5, YMMWORD PTR [rdi+1728]
	vpsubq ymm5, ymm5, ymm15
	vpblendd ymm15, ymm15, ymm5, 204
	vpaddq ymm15, ymm10, ymm15
	vpblendd ymm10, ymm15, ymm10, 3
	vpunpcklqdq ymm15, ymm1, ymm1
	vpunpckhqdq ymm11, ymm1, ymm1
	vmovdqu ymm6, YMMWORD PTR [rdi+1760]
	vpsubq ymm6, ymm6, ymm15
	vpblendd ymm15, ymm15, ymm6, 204
	vpaddq ymm15, ymm11, ymm15
	vpblendd ymm11, ymm15, ymm11, 3
	vpunpcklqdq ymm15, ymm2, ymm2
	vpunpckhqdq ymm12, ymm2, ymm2
	vmovdqu ymm7, YMMWORD PTR [rdi+1760]
	vpsubq ymm7, ymm7, ymm15
	vpblendd ymm15, ymm15, ymm7, 204
	vpaddq ymm15, ymm12, ymm15
	vpblendd ymm12, ymm15, ymm12, 3
	vpunpcklqdq ymm15, ymm3, ymm3
	vpunpckhqdq ymm13, ymm3, ymm3
	vmovdqu ymm8, YMMWORD PTR [rdi+1760]
	vpsubq ymm8, ymm8, ymm15
	vpblendd ymm15, ymm15, ymm8, 204
	vpaddq ymm15, ymm13, ymm15
	vpblendd ymm13, ymm15, ymm13, 3
	vpunpcklqdq ymm15, ymm4, ymm4
	vpunpckhqdq ymm14, ymm4, ymm4
	vmovdqu ymm9, YMMWORD PTR [rdi+1760]
	vpsubq ymm9, ymm9, ymm15
	vpblendd ymm15, ymm15, ymm9, 204
	vpaddq ymm15, ymm14, ymm15
	vpblendd ymm14, ymm15, ymm14, 3
	vmovdqu ymm15, YMMWORD PTR [rdi+1664]
	vpsrlq ymm5, ymm14, 51
	vpand ymm14, ymm14, ymm15
	vpsrlq ymm6, ymm13, 51
	vpand ymm13, ymm13, ymm15
	vpaddq ymm14, ymm14, ymm6
	vpsrlq ymm6, ymm12, 51
	vpand ymm12, ymm12, ymm15
	vpaddq ymm13, ymm13, ymm6
	vpsrlq ymm6, ymm11, 51
	vpand ymm11, ymm11, ymm15
	vpaddq ymm12, ymm12, ymm6
	vpsrlq ymm6, ymm10, 51
	vpand ymm10, ymm10, ymm15
	vpaddq ymm11, ymm11, ymm6
	vmovdqu ymm6, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm10, ymm5, ymm6
	vmovdqu ymm5, YMMWORD PTR [rdi+1792]
	vpblendd ymm5, ymm10, ymm5, 15
	vmovdqu ymm6, YMMWORD PTR [rdi+1824]
	vpblendd ymm6, ymm11, ymm6, 15
	vmovdqu ymm7, YMMWORD PTR [rdi+1856]
	vpblendd ymm7, ymm12, ymm7, 15
	vmovdqu ymm8, YMMWORD PTR [rdi+1888]
	vpblendd ymm8, ymm13, ymm8, 15
	vmovdqu ymm9, YMMWORD PTR [rdi+1920]
	vpblendd ymm9, ymm14, ymm9, 15
	vpxor ymm15, ymm15, ymm15
	vpblendd ymm0, ymm15, ymm0, 15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm17, ymm11, ymm9
	vpmadd52huq ymm18, ymm11, ymm8
	vpmadd52luq ymm17, ymm12, ymm8
	vpmadd52huq ymm18, ymm12, ymm7
	vpmadd52luq ymm17, ymm13, ymm7
	vpmadd52huq ymm18, ymm13, ymm6
	vpmadd52luq ymm17, ymm14, ymm6
	vpmadd52huq ymm18, ymm14, ymm5
	vpmadd52luq ymm0, ymm10, ymm5
	vpmadd52huq ymm18, ymm10, ymm9
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm0, ymm0, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm0, ymm0, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm0, ymm0, ymm18
	vpblendd ymm1, ymm15, ymm1, 15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm1, ymm11, ymm5
	vpmadd52huq ymm18, ymm11, ymm9
	vpmadd52luq ymm17, ymm12, ymm9
	vpmadd52huq ymm18, ymm12, ymm8
	vpmadd52luq ymm17, ymm13, ymm8
	vpmadd52huq ymm18, ymm13, ymm7
	vpmadd52luq ymm17, ymm14, ymm7
	vpmadd52huq ymm18, ymm14, ymm6
	vpmadd52luq ymm1, ymm10, ymm6
	vpmadd52huq ymm16, ymm10, ymm5
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm1, ymm1, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm1, ymm1, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm1, ymm1, ymm18
	vpblendd ymm2, ymm15, ymm2, 15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm2, ymm11, ymm6
	vpmadd52huq ymm16, ymm11, ymm5
	vpmadd52luq ymm2, ymm12, ymm5
	vpmadd52huq ymm18, ymm12, ymm9
	vpmadd52luq ymm17, ymm13, ymm9
	vpmadd52huq ymm18, ymm13, ymm8
	vpmadd52luq ymm17, ymm14, ymm8
	vpmadd52huq ymm18, ymm14, ymm7
	vpmadd52luq ymm2, ymm10, ymm7
	vpmadd52huq ymm16, ymm10, ymm6
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm2, ymm2, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm2, ymm2, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm2, ymm2, ymm18
	vpblendd ymm3, ymm15, ymm3, 15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm3, ymm11, ymm7
	vpmadd52huq ymm16, ymm11, ymm6
	vpmadd52luq ymm3, ymm12, ymm6
	vpmadd52huq ymm16, ymm12, ymm5
	vpmadd52luq ymm3, ymm13, ymm5
	vpmadd52huq ymm18, ymm13, ymm9
	vpmadd52luq ymm17, ymm14, ymm9
	vpmadd52huq ymm18, ymm14, ymm8
	vpmadd52luq ymm3, ymm10, ymm8
	vpmadd52huq ymm16, ymm10, ymm7
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm3, ymm3, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm3, ymm3, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm3, ymm3, ymm18
	vpblendd ymm4, ymm15, ymm4, 15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm4, ymm11, ymm8
	vpmadd52huq ymm16, ymm11, ymm7
	vpmadd52luq ymm4, ymm12, ymm7
	vpmadd52huq ymm16, ymm12, ymm6
	vpmadd52luq ymm4, ymm13, ymm6
	vpmadd52huq ymm16, ymm13, ymm5
	vpmadd52luq ymm4, ymm14, ymm5
	vpmadd52huq ymm18, ymm14, ymm9
	vpmadd52luq ymm4, ymm10, ymm9
	vpmadd52huq ymm16, ymm10, ymm8
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm4, ymm4, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm4, ymm4, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm4, ymm4, ymm18
	vmovdqu ymm15, YMMWORD PTR [rdi+1664]
	vpsrlq ymm5, ymm4, 51
	vpand ymm4, ymm4, ymm15
	vpsrlq ymm6, ymm3, 51
	vpand ymm3, ymm3, ymm15
	vpaddq ymm4, ymm4, ymm6
	vpsrlq ymm6, ymm2, 51
	vpand ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm6
	vpsrlq ymm6, ymm1, 51
	vpand ymm1, ymm1, ymm15
	vpaddq ymm2, ymm2, ymm6
	vpsrlq ymm6, ymm0, 51
	vpand ymm0, ymm0, ymm15
	vpaddq ymm1, ymm1, ymm6
	vmovdqu ymm6, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm5, ymm6
	vpblendd ymm10, ymm10, ymm0, 240
	vmovdqu ymm5, YMMWORD PTR [rdi+1952]
	vpblendd ymm5, ymm0, ymm5, 240
	vpblendd ymm11, ymm11, ymm1, 240
	vmovdqu ymm6, YMMWORD PTR [rdi+1984]
	vpblendd ymm6, ymm1, ymm6, 240
	vpblendd ymm12, ymm12, ymm2, 240
	vmovdqu ymm7, YMMWORD PTR [rdi+2016]
	vpblendd ymm7, ymm2, ymm7, 240
	vpblendd ymm13, ymm13, ymm3, 240
	vmovdqu ymm8, YMMWORD PTR [rdi+2048]
	vpblendd ymm8, ymm3, ymm8, 240
	vpblendd ymm14, ymm14, ymm4, 240
	vmovdqu ymm9, YMMWORD PTR [rdi+2080]
	vpblendd ymm9, ymm4, ymm9, 240
	vpxor ymm0, ymm0, ymm0
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm17, ymm11, ymm9
	vpmadd52huq ymm18, ymm11, ymm8
	vpmadd52luq ymm17, ymm12, ymm8
	vpmadd52huq ymm18, ymm12, ymm7
	vpmadd52luq ymm17, ymm13, ymm7
	vpmadd52huq ymm18, ymm13, ymm6
	vpmadd52luq ymm17, ymm14, ymm6
	vpmadd52huq ymm18, ymm14, ymm5
	vpmadd52luq ymm0, ymm10, ymm5
	vpmadd52huq ymm18, ymm10, ymm9
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm0, ymm0, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm0, ymm0, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm0, ymm0, ymm18
	vpxor ymm1, ymm1, ymm1
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm1, ymm11, ymm5
	vpmadd52huq ymm18, ymm11, ymm9
	vpmadd52luq ymm17, ymm12, ymm9
	vpmadd52huq ymm18, ymm12, ymm8
	vpmadd52luq ymm17, ymm13, ymm8
	vpmadd52huq ymm18, ymm13, ymm7
	vpmadd52luq ymm17, ymm14, ymm7
	vpmadd52huq ymm18, ymm14, ymm6
	vpmadd52luq ymm1, ymm10, ymm6
	vpmadd52huq ymm16, ymm10, ymm5
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm1, ymm1, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm1, ymm1, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm1, ymm1, ymm18
	vpxor ymm2, ymm2, ymm2
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm2, ymm11, ymm6
	vpmadd52huq ymm16, ymm11, ymm5
	vpmadd52luq ymm2, ymm12, ymm5
	vpmadd52huq ymm18, ymm12, ymm9
	vpmadd52luq ymm17, ymm13, ymm9
	vpmadd52huq ymm18, ymm13, ymm8
	vpmadd52luq ymm17, ymm14, ymm8
	vpmadd52huq ymm18, ymm14, ymm7
	vpmadd52luq ymm2, ymm10, ymm7
	vpmadd52huq ymm16, ymm10, ymm6
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm2, ymm2, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm2, ymm2, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm2, ymm2, ymm18
	vpxor ymm3, ymm3, ymm3
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm3, ymm11, ymm7
	vpmadd52huq ymm16, ymm11, ymm6
	vpmadd52luq ymm3, ymm12, ymm6
	vpmadd52huq ymm16, ymm12, ymm5
	vpmadd52luq ymm3, ymm13, ymm5
	vpmadd52huq ymm18, ymm13, ymm9
	vpmadd52luq ymm17, ymm14, ymm9
	vpmadd52huq ymm18, ymm14, ymm8
	vpmadd52luq ymm3, ymm10, ymm8
	vpmadd52huq ymm16, ymm10, ymm7
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm3, ymm3, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm3, ymm3, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm3, ymm3, ymm18
	vpxor ymm4, ymm4, ymm4
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm4, ymm11, ymm8
	vpmadd52huq ymm16, ymm11, ymm7
	vpmadd52luq ymm4, ymm12, ymm7
	vpmadd52huq ymm16, ymm12, ymm6
	vpmadd52luq ymm4, ymm13, ymm6
	vpmadd52huq ymm16, ymm13, ymm5
	vpmadd52luq ymm4, ymm14, ymm5
	vpmadd52huq ymm18, ymm14, ymm9
	vpmadd52luq ymm4, ymm10, ymm9
	vpmadd52huq ymm16, ymm10, ymm8
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm4, ymm4, ymm16
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm17, ymm17, ymm18
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm18, ymm17, ymm17
	vpaddq ymm4, ymm4, ymm18
	vpsllq ymm18, ymm17, 4
	vpaddq ymm4, ymm4, ymm18
	test rbx, rbx
	jne 21b
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm11
	vpsrlq ymm11, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm11
	vpsrlq ymm11, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm11
	vpsrlq ymm11, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm11
	vmovdqu ymm11, YMMWORD PTR [rdi+2112]
	vpand ymm12, ymm1, ymm11
	vpsllq ymm12, ymm12, 51
	vpor ymm5, ymm0, ymm12
	vpsrlq ymm6, ymm1, 13
	vmovdqu ymm11, YMMWORD PTR [rdi+2144]
	vpand ymm12, ymm2, ymm11
	vpsllq ymm12, ymm12, 38
	vpor ymm6, ymm6, ymm12
	vpsrlq ymm7, ymm2, 26
	vmovdqu ymm11, YMMWORD PTR [rdi+2176]
	vpand ymm12, ymm3, ymm11
	vpsllq ymm12, ymm12, 25
	vpor ymm7, ymm7, ymm12
	vpsrlq ymm8, ymm3, 39
	vpsllq ymm12, ymm4, 12
	vpor ymm8, ymm8, ymm12
	vpunpcklqdq ymm0, ymm5, ymm6
	vpunpckhqdq ymm1, ymm5, ymm6
	vpunpcklqdq ymm2, ymm7, ymm8
	vpunpckhqdq ymm3, ymm7, ymm8
	vperm2i128 ymm5, ymm0, ymm2, 32
	vperm2i128 ymm6, ymm1, ymm3, 32
	vperm2i128 ymm7, ymm0, ymm2, 49
	vperm2i128 ymm8, ymm1, ymm3, 49
	vmovdqu YMMWORD PTR [rdi+96], ymm5
	vmovdqu YMMWORD PTR [rdi+128], ymm6
	vmovdqu YMMWORD PTR [rdi+160], ymm7
	vmovdqu YMMWORD PTR [rdi+192], ymm8
	vzeroupper
	lfence
	mov DWORD PTR [rdi+2208], r11d
	ldmxcsr DWORD PTR [rdi+2208]
	mov rdx, QWORD PTR [rdi+640]
	mov ecx, 0
	sub rcx, rdx
	mov r8, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+120]
	mov r12, QWORD PTR [rdi+160]
	mov r13, QWORD PTR [rdi+168]
	mov r14, QWORD PTR [rdi+176]
	mov r15, QWORD PTR [rdi+184]
	mov rax, r8
	xor rax, r12
	and rax, rcx
	xor r8, rax
	xor r12, rax
	mov rax, r9
	xor rax, r13
	and rax, rcx
	xor r9, rax
	xor r13, rax
	mov rax, r10
	xor rax, r14
	and rax, rcx
	xor r10, rax
	xor r14, rax
	mov rax, r11
	xor rax, r15
	and rax, rcx
	xor r11, rax
	xor r15, rax
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov QWORD PTR [rdi+184], r15
	mov r8, QWORD PTR [rdi+128]
	mov r9, QWORD PTR [rdi+136]
	mov r10, QWORD PTR [rdi+144]
	mov r11, QWORD PTR [rdi+152]
	mov r12, QWORD PTR [rdi+192]
	mov r13, QWORD PTR [rdi+200]
	mov r14, QWORD PTR [rdi+208]
	mov r15, QWORD PTR [rdi+216]
	mov rax, r8
	xor rax, r12
	and rax, rcx
	xor r8, rax
	xor r12, rax
	mov rax, r9
	xor rax, r13
	and rax, rcx
	xor r9, rax
	xor r13, rax
	mov rax, r10
	xor rax, r14
	and rax, rcx
	xor r10, rax
	xor r14, rax
	mov rax, r11
	xor rax, r15
	and rax, rcx
	xor r11, rax
	xor r15, rax
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+192], r12
	mov QWORD PTR [rdi+200], r13
	mov QWORD PTR [rdi+208], r14
	mov QWORD PTR [rdi+216], r15
	call {vg_gf25519_r64_invert}
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+96]
	mulx r10, rax, QWORD PTR [rdi+104]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+120]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
	shl r11, 1
	adc r12, r12
	shr r11, 1
	imul rax, r12, 19
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r8, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+120]
	mov rax, r11
	shr rax, 63
	movabs rdx, 9223372036854775807
	and r11, rdx
	mov ecx, 0
	sub rcx, rax
	and rcx, 19
	add r8, rcx
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov r12, r8
	add r12, 19
	mov r13, r9
	adc r13, 0
	mov r14, r10
	adc r14, 0
	mov r15, r11
	adc r15, 0
	mov rax, r15
	shr rax, 63
	and r15, rdx
	mov ecx, 0
	sub rcx, rax
	xor r12, r8
	and r12, rcx
	xor r8, r12
	xor r13, r9
	and r13, rcx
	xor r9, r13
	xor r14, r10
	and r14, rcx
	xor r10, r14
	xor r15, r11
	and r15, rcx
	xor r11, r15
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	ret
	.p2align 6
