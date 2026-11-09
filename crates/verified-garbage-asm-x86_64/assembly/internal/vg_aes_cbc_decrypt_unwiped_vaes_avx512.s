// The functions of `src/internal/vg_aes_cbc_decrypt_unwiped_vaes_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_decrypt_unwiped_vaes_avx512:
	mov r11, rdx
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	movdqu xmm15, XMMWORD PTR [r11]
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+16], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+32], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+48], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+64], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+80], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+96], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+112], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+128], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+144], xmm8
	cmp rsi, 10
	je 20f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+160], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+176], xmm8
	cmp rsi, 12
	je 22f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+192], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+208], xmm8
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	cmp rcx, 8
	cmp rcx, 32
	jb 24f
26:
	vmovdqu32 zmm0, ZMMWORD PTR [rdx]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+64]
	vmovdqu32 zmm2, ZMMWORD PTR [rdx+128]
	vmovdqu32 zmm3, ZMMWORD PTR [rdx+192]
	vmovdqu32 zmm4, ZMMWORD PTR [rdx+256]
	vmovdqu32 zmm5, ZMMWORD PTR [rdx+320]
	vmovdqu32 zmm6, ZMMWORD PTR [rdx+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+448]
	vbroadcasti32x4 zmm8, XMMWORD PTR [r10]
	vpxord zmm0, zmm0, zmm8
	vpxord zmm1, zmm1, zmm8
	vpxord zmm2, zmm2, zmm8
	vpxord zmm3, zmm3, zmm8
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm8
	vpxord zmm6, zmm6, zmm8
	vpxord zmm7, zmm7, zmm8
	cmp rsi, 10
	je 27f
	cmp rsi, 12
	je 29f
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+208]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+192]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	jmp 210f
29:
210:
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+176]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+160]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	jmp 28f
27:
28:
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+144]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+128]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+112]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+96]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+80]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+64]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+48]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+32]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+16]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vaesdec zmm4, zmm4, zmm8
	vaesdec zmm5, zmm5, zmm8
	vaesdec zmm6, zmm6, zmm8
	vaesdec zmm7, zmm7, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi]
	vaesdeclast zmm0, zmm0, zmm8
	vaesdeclast zmm1, zmm1, zmm8
	vaesdeclast zmm2, zmm2, zmm8
	vaesdeclast zmm3, zmm3, zmm8
	vaesdeclast zmm4, zmm4, zmm8
	vaesdeclast zmm5, zmm5, zmm8
	vaesdeclast zmm6, zmm6, zmm8
	vaesdeclast zmm7, zmm7, zmm8
	vmovdqu32 zmm14, ZMMWORD PTR [rdx]
	vshufi32x4 zmm15, zmm15, zmm14, 0
	vshufi32x4 zmm15, zmm15, zmm14, 152
	vpxord zmm0, zmm0, zmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+48]
	vmovdqu32 ZMMWORD PTR [rdx], zmm0
	vmovdqu32 zmm14, ZMMWORD PTR [rdx+64]
	vshufi32x4 zmm15, zmm15, zmm14, 0
	vshufi32x4 zmm15, zmm15, zmm14, 152
	vpxord zmm1, zmm1, zmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+112]
	vmovdqu32 ZMMWORD PTR [rdx+64], zmm1
	vmovdqu32 zmm14, ZMMWORD PTR [rdx+128]
	vshufi32x4 zmm15, zmm15, zmm14, 0
	vshufi32x4 zmm15, zmm15, zmm14, 152
	vpxord zmm2, zmm2, zmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+176]
	vmovdqu32 ZMMWORD PTR [rdx+128], zmm2
	vmovdqu32 zmm14, ZMMWORD PTR [rdx+192]
	vshufi32x4 zmm15, zmm15, zmm14, 0
	vshufi32x4 zmm15, zmm15, zmm14, 152
	vpxord zmm3, zmm3, zmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+240]
	vmovdqu32 ZMMWORD PTR [rdx+192], zmm3
	vmovdqu32 zmm14, ZMMWORD PTR [rdx+256]
	vshufi32x4 zmm15, zmm15, zmm14, 0
	vshufi32x4 zmm15, zmm15, zmm14, 152
	vpxord zmm4, zmm4, zmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+304]
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm4
	vmovdqu32 zmm14, ZMMWORD PTR [rdx+320]
	vshufi32x4 zmm15, zmm15, zmm14, 0
	vshufi32x4 zmm15, zmm15, zmm14, 152
	vpxord zmm5, zmm5, zmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+368]
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm5
	vmovdqu32 zmm14, ZMMWORD PTR [rdx+384]
	vshufi32x4 zmm15, zmm15, zmm14, 0
	vshufi32x4 zmm15, zmm15, zmm14, 152
	vpxord zmm6, zmm6, zmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+432]
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm6
	vmovdqu32 zmm14, ZMMWORD PTR [rdx+448]
	vshufi32x4 zmm15, zmm15, zmm14, 0
	vshufi32x4 zmm15, zmm15, zmm14, 152
	vpxord zmm7, zmm7, zmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+496]
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm7
	add rdx, 512
	sub rcx, 32
	cmp rcx, 32
	jae 26b
	jmp 25f
24:
25:
	cmp rcx, 16
	jb 211f
213:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vmovdqu ymm2, YMMWORD PTR [rdx+64]
	vmovdqu ymm3, YMMWORD PTR [rdx+96]
	vmovdqu ymm4, YMMWORD PTR [rdx+128]
	vmovdqu ymm5, YMMWORD PTR [rdx+160]
	vmovdqu ymm6, YMMWORD PTR [rdx+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vbroadcasti128 ymm8, XMMWORD PTR [r10]
	vpxor ymm0, ymm0, ymm8
	vpxor ymm1, ymm1, ymm8
	vpxor ymm2, ymm2, ymm8
	vpxor ymm3, ymm3, ymm8
	vpxor ymm4, ymm4, ymm8
	vpxor ymm5, ymm5, ymm8
	vpxor ymm6, ymm6, ymm8
	vpxor ymm7, ymm7, ymm8
	cmp rsi, 10
	je 214f
	cmp rsi, 12
	je 216f
	vbroadcasti128 ymm8, XMMWORD PTR [r8+208]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+192]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	jmp 217f
216:
217:
	vbroadcasti128 ymm8, XMMWORD PTR [r8+176]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+160]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	jmp 215f
214:
215:
	vbroadcasti128 ymm8, XMMWORD PTR [r8+144]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+128]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+112]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+96]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+80]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+64]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+48]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+32]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+16]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vaesdec ymm4, ymm4, ymm8
	vaesdec ymm5, ymm5, ymm8
	vaesdec ymm6, ymm6, ymm8
	vaesdec ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi]
	vaesdeclast ymm0, ymm0, ymm8
	vaesdeclast ymm1, ymm1, ymm8
	vaesdeclast ymm2, ymm2, ymm8
	vaesdeclast ymm3, ymm3, ymm8
	vaesdeclast ymm4, ymm4, ymm8
	vaesdeclast ymm5, ymm5, ymm8
	vaesdeclast ymm6, ymm6, ymm8
	vaesdeclast ymm7, ymm7, ymm8
	vextracti128 xmm14, ymm0, 1
	vpxor xmm0, xmm0, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm14, xmm14, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm14
	vextracti128 xmm14, ymm1, 1
	vpxor xmm1, xmm1, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm1
	vpxor xmm14, xmm14, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm14
	vextracti128 xmm14, ymm2, 1
	vpxor xmm2, xmm2, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm2
	vpxor xmm14, xmm14, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm14
	vextracti128 xmm14, ymm3, 1
	vpxor xmm3, xmm3, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm3
	vpxor xmm14, xmm14, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm14
	vextracti128 xmm14, ymm4, 1
	vpxor xmm4, xmm4, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+128]
	vmovdqu XMMWORD PTR [rdx+128], xmm4
	vpxor xmm14, xmm14, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+144]
	vmovdqu XMMWORD PTR [rdx+144], xmm14
	vextracti128 xmm14, ymm5, 1
	vpxor xmm5, xmm5, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+160]
	vmovdqu XMMWORD PTR [rdx+160], xmm5
	vpxor xmm14, xmm14, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+176]
	vmovdqu XMMWORD PTR [rdx+176], xmm14
	vextracti128 xmm14, ymm6, 1
	vpxor xmm6, xmm6, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+192]
	vmovdqu XMMWORD PTR [rdx+192], xmm6
	vpxor xmm14, xmm14, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+208]
	vmovdqu XMMWORD PTR [rdx+208], xmm14
	vextracti128 xmm14, ymm7, 1
	vpxor xmm7, xmm7, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+224]
	vmovdqu XMMWORD PTR [rdx+224], xmm7
	vpxor xmm14, xmm14, xmm15
	vmovdqu xmm15, XMMWORD PTR [rdx+240]
	vmovdqu XMMWORD PTR [rdx+240], xmm14
	add rdx, 256
	sub rcx, 16
	cmp rcx, 16
	jae 213b
	jmp 212f
211:
212:
	vzeroupper
	cmp rcx, 8
	jb 218f
220:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	cmp rsi, 10
	je 221f
	cmp rsi, 12
	je 223f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	jmp 224f
223:
224:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	jmp 222f
221:
222:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	aesdeclast xmm3, xmm8
	aesdeclast xmm4, xmm8
	aesdeclast xmm5, xmm8
	aesdeclast xmm6, xmm8
	aesdeclast xmm7, xmm8
	pxor xmm0, xmm15
	movdqu xmm15, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdx], xmm0
	pxor xmm1, xmm15
	movdqu xmm15, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdx+16], xmm1
	pxor xmm2, xmm15
	movdqu xmm15, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdx+32], xmm2
	pxor xmm3, xmm15
	movdqu xmm15, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdx+48], xmm3
	pxor xmm4, xmm15
	movdqu xmm15, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdx+64], xmm4
	pxor xmm5, xmm15
	movdqu xmm15, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdx+80], xmm5
	pxor xmm6, xmm15
	movdqu xmm15, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdx+96], xmm6
	pxor xmm7, xmm15
	movdqu xmm15, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdx+112], xmm7
	add rdx, 128
	sub rcx, 8
	cmp rcx, 8
	jae 220b
	jmp 219f
218:
219:
	test rcx, rcx
	je 225f
227:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	cmp rsi, 10
	je 228f
	cmp rsi, 12
	je 230f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	jmp 231f
230:
231:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	jmp 229f
228:
229:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	pxor xmm0, xmm15
	movdqu xmm15, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdx], xmm0
	add rdx, 16
	sub rcx, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r11], xmm15
	ret
	.p2align 6
