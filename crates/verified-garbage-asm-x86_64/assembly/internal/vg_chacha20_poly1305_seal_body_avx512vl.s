// The functions of `src/internal/vg_chacha20_poly1305_seal_body_avx512vl.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_body_avx512vl:
	lea rsp, [rsp-1728]
	mov rax, QWORD PTR [rsp+1736]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov r11, QWORD PTR [rsp+8]
	mov QWORD PTR [rax], rbx
	mov QWORD PTR [rax+8], rbp
	mov QWORD PTR [rax+16], r13
	mov QWORD PTR [rax+24], r14
	mov QWORD PTR [rax+32], r15
	mov QWORD PTR [rax+40], r12
	mov r15, rax
	mov r12, r11
	mov rbx, rdx
	mov rbp, rcx
	mov r14, r8
	mov r13, r9
	movabs rax, 3684054920433006693
	mov QWORD PTR [r15+64], rax
	movabs rax, 7719281312240119090
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r15+80], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r15+104], rax
	mov eax, DWORD PTR [rsi]
	shl rax, 32
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [rsi+4]
	mov QWORD PTR [r15+120], rax
	movabs rax, 3684054920433006693
	mov QWORD PTR [r15+608], rax
	movabs rax, 7719281312240119090
	mov QWORD PTR [r15+616], rax
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r15+624], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r15+632], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r15+640], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r15+648], rax
	mov eax, DWORD PTR [rsi]
	shl rax, 32
	mov QWORD PTR [r15+656], rax
	mov rax, QWORD PTR [rsi+4]
	mov QWORD PTR [r15+664], rax
	cmp r13, 449
	jae 20f
	mov rdx, r13
	jmp 21f
20:
	cmp r13, 1409
	jb 22f
	mov rdx, r13
	sub rdx, 1
	and rdx, 511
	add rdx, -448
	sbb rdx, rdx
	and rdx, 448
	jmp 23f
22:
	mov edx, 448
23:
21:
	mov QWORD PTR [r15+48], rdx
	add rdx, 64
	vpxor ymm0, ymm0, ymm0
	mov ecx, 0
24:
	vmovdqu YMMWORD PTR [r15+rcx*1+672], ymm0
	add rcx, 32
	cmp rcx, rdx
	jb 24b
	vzeroupper
	mov rdi, r15
	add rdi, 608
	mov rsi, r15
	add rsi, 672
	mov rcx, r15
	add rcx, 128
	mov r8, rsi
	call {vg_chacha20_xor_avx512vl}
	mov r15, rsi
	sub r15, 128
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 672
	call {vg_poly1305_init_core}
	mov r15, rdi
	sub r15, 448
	mov rdi, r15
	add rdi, 448
	mov rsi, rbx
	mov rdx, rbp
	shr rdx, 4
	je 25f
	call {vg_poly1305_blocks_avx2}
	mov r15, rdi
	sub r15, 448
	jmp 26f
25:
26:
	mov rdx, rbp
	and rdx, 15
	jne 27f
	je 29f
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	add rax, 1
	add rax, 1
	jmp 210f
29:
210:
28:
	mov QWORD PTR [r15+592], rbp
	mov QWORD PTR [r15+600], r13
	cmp r13, 449
	jb 219f
	mov rdx, QWORD PTR [r15+48]
	test rdx, rdx
	je 221f
	cmp r13, 449
	jae 223f
	mov rdx, r13
	jmp 224f
223:
	cmp r13, 1409
	jb 225f
	mov rdx, r13
	sub rdx, 1
	and rdx, 511
	add rdx, -448
	sbb rdx, rdx
	and rdx, 448
	jmp 226f
225:
	mov edx, 448
226:
224:
	test rdx, rdx
	je 227f
	mov rsi, r15
	add rsi, 736
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 229f
231:
	vmovdqu ymm0, YMMWORD PTR [r14+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [r14+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 231b
	jmp 230f
229:
230:
	mov rdi, r14
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 232f
234:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 234b
	jmp 233f
232:
233:
	cmp rcx, rdx
	je 235f
237:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 237b
	jmp 236f
235:
236:
	jmp 228f
227:
228:
	cmp r13, 449
	jae 238f
	mov rdx, r13
	jmp 239f
238:
	cmp r13, 1409
	jb 240f
	mov rdx, r13
	sub rdx, 1
	and rdx, 511
	add rdx, -448
	sbb rdx, rdx
	and rdx, 448
	jmp 241f
240:
	mov edx, 448
241:
239:
	mov rax, rdx
	shr rax, 6
	add rax, 1
	mov DWORD PTR [r15+112], eax
	mov rsi, r14
	add rsi, rdx
	mov rax, r13
	sub rax, rdx
	mov rdx, rax
	mov rdi, r15
	add rdi, 64
	mov rcx, r15
	add rcx, 128
	mov rsi, r14
	cmp rdx, 513
	jb 242f
	mov QWORD PTR [rcx+392], r12
	mov QWORD PTR [rcx+400], r13
	mov QWORD PTR [rcx+408], r14
	mov QWORD PTR [rcx+416], rdx
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
	mov rdi, rcx
	add rdi, 320
	movabs rax, 1152921487695413247
	mov r8, QWORD PTR [rdi+24]
	and r8, rax
	movabs rax, 1152921487695413244
	mov r9, QWORD PTR [rdi+32]
	and r9, rax
	mov r10, r9
	shr r10, 2
	add r10, r9
	mov r11, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	mov rdi, rcx
	sub rdi, 64
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add rsi, 448
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
	mov rdx, QWORD PTR [rcx+416]
	sub rdx, 512
	mov QWORD PTR [rcx+416], rdx
	cmp rdx, 512
	jb 244f
246:
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+448]
	adc rbx, QWORD PTR [rsi+456]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+464]
	adc rbx, QWORD PTR [rsi+472]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+480]
	adc rbx, QWORD PTR [rsi+488]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+496]
	adc rbx, QWORD PTR [rsi+504]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vmovdqu YMMWORD PTR [rcx+64], ymm14
	vmovdqu YMMWORD PTR [rcx+96], ymm15
	vmovdqu ymm15, YMMWORD PTR [rcx+128]
	add rsi, 512
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
	mov rdx, QWORD PTR [rcx+416]
	sub rdx, 512
	mov QWORD PTR [rcx+416], rdx
	cmp rdx, 512
	jae 246b
	jmp 245f
244:
245:
	mov rdx, QWORD PTR [rcx+416]
	sub rdx, 1
	cmp rdx, 256
	jb 247f
	mov eax, 0
	mov eax, 0
	mov eax, 0
	mov eax, eax
	mov eax, eax
	cmp rdx, 448
	jb 249f
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	mov rbp, QWORD PTR [rcx+416]
	add rbp, 512
	mov rdx, QWORD PTR [rcx+416]
	add rsi, 512
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	jmp 250f
249:
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+448]
	adc rbx, QWORD PTR [rsi+456]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+464]
	adc rbx, QWORD PTR [rsi+472]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+480]
	adc rbx, QWORD PTR [rsi+488]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+496]
	adc rbx, QWORD PTR [rsi+504]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	vmovdqu XMMWORD PTR [rcx+608], xmm0
	vextracti128 xmm13, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+864], xmm13
	vmovdqu XMMWORD PTR [rcx+672], xmm1
	vextracti128 xmm13, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+928], xmm13
	vmovdqu XMMWORD PTR [rcx+736], xmm2
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+992], xmm13
	vmovdqu XMMWORD PTR [rcx+800], xmm3
	vextracti128 xmm13, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1056], xmm13
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
	vmovdqu XMMWORD PTR [rcx+624], xmm4
	vextracti128 xmm13, ymm4, 1
	vmovdqu XMMWORD PTR [rcx+880], xmm13
	vmovdqu XMMWORD PTR [rcx+688], xmm5
	vextracti128 xmm13, ymm5, 1
	vmovdqu XMMWORD PTR [rcx+944], xmm13
	vmovdqu XMMWORD PTR [rcx+752], xmm6
	vextracti128 xmm13, ymm6, 1
	vmovdqu XMMWORD PTR [rcx+1008], xmm13
	vmovdqu XMMWORD PTR [rcx+816], xmm7
	vextracti128 xmm13, ymm7, 1
	vmovdqu XMMWORD PTR [rcx+1072], xmm13
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
	vmovdqu XMMWORD PTR [rcx+656], xmm8
	vextracti128 xmm13, ymm8, 1
	vmovdqu XMMWORD PTR [rcx+912], xmm13
	vmovdqu XMMWORD PTR [rcx+720], xmm9
	vextracti128 xmm13, ymm9, 1
	vmovdqu XMMWORD PTR [rcx+976], xmm13
	vmovdqu XMMWORD PTR [rcx+784], xmm10
	vextracti128 xmm13, ymm10, 1
	vmovdqu XMMWORD PTR [rcx+1040], xmm13
	vmovdqu XMMWORD PTR [rcx+848], xmm11
	vextracti128 xmm13, ymm11, 1
	vmovdqu XMMWORD PTR [rcx+1104], xmm13
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
	vmovdqu XMMWORD PTR [rcx+640], xmm0
	vextracti128 xmm13, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+896], xmm13
	vmovdqu XMMWORD PTR [rcx+704], xmm1
	vextracti128 xmm13, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+960], xmm13
	vmovdqu XMMWORD PTR [rcx+768], xmm2
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1024], xmm13
	vmovdqu XMMWORD PTR [rcx+832], xmm3
	vextracti128 xmm13, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1088], xmm13
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 512
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
	mov rsi, rcx
	add rsi, 608
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 251f
253:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 253b
	jmp 252f
251:
252:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 254f
256:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 256b
	jmp 255f
254:
255:
	cmp rcx, rdx
	je 257f
259:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 259b
	jmp 258f
257:
258:
	vzeroupper
	mov rcx, r9
	mov edx, 0
	mov eax, 0
	mov eax, 0
	mov eax, 0
	mov eax, 0
	mov eax, 0
	mov eax, eax
	mov eax, eax
250:
	jmp 248f
247:
	cmp rdx, 128
	jb 260f
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
	mov r12, r9
	mov r9, rcx
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
	mov r9, r12
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+448]
	adc rbx, QWORD PTR [rsi+456]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+464]
	adc rbx, QWORD PTR [rsi+472]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+480]
	adc rbx, QWORD PTR [rsi+488]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+496]
	adc rbx, QWORD PTR [rsi+504]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 512
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
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
	mov rsi, r9
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 262f
264:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 264b
	jmp 263f
262:
263:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 265f
267:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 267b
	jmp 266f
265:
266:
	cmp rcx, rdx
	je 268f
270:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 270b
	jmp 269f
268:
269:
	vzeroupper
	mov rcx, r9
	mov edx, 0
	jmp 261f
260:
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
	mov r12, r9
	mov r9, rcx
	vmovdqu ymm8, YMMWORD PTR [r9+128]
	vmovdqu ymm9, YMMWORD PTR [r9+160]
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vbroadcasti128 ymm1, XMMWORD PTR [rdi+16]
	vbroadcasti128 ymm2, XMMWORD PTR [rdi+32]
	vbroadcasti128 ymm3, XMMWORD PTR [rdi+48]
	vpaddd ymm3, ymm3, ymm12
	mov r9, r12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+448]
	adc rbx, QWORD PTR [rsi+456]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+464]
	adc rbx, QWORD PTR [rsi+472]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+480]
	adc rbx, QWORD PTR [rsi+488]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+496]
	adc rbx, QWORD PTR [rsi+504]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 512
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
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
	mov rsi, r9
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 271f
273:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 273b
	jmp 272f
271:
272:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 274f
276:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 276b
	jmp 275f
274:
275:
	cmp rcx, rdx
	je 277f
279:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 279b
	jmp 278f
277:
278:
	vzeroupper
	mov rcx, r9
	mov edx, 0
261:
248:
	jmp 243f
242:
	mov QWORD PTR [rcx+392], r12
	mov QWORD PTR [rcx+400], r13
	mov QWORD PTR [rcx+408], r14
	mov QWORD PTR [rcx+416], rdx
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
	mov rdi, rcx
	add rdi, 320
	movabs rax, 1152921487695413247
	mov r8, QWORD PTR [rdi+24]
	and r8, rax
	movabs rax, 1152921487695413244
	mov r9, QWORD PTR [rdi+32]
	and r9, rax
	mov r10, r9
	shr r10, 2
	add r10, r9
	mov r11, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	mov rdi, rcx
	sub rdi, 64
	mov rdx, QWORD PTR [rcx+416]
	sub rdx, 1
	cmp rdx, 256
	jb 280f
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	vmovdqu XMMWORD PTR [rcx+608], xmm0
	vextracti128 xmm13, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+864], xmm13
	vmovdqu XMMWORD PTR [rcx+672], xmm1
	vextracti128 xmm13, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+928], xmm13
	vmovdqu XMMWORD PTR [rcx+736], xmm2
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+992], xmm13
	vmovdqu XMMWORD PTR [rcx+800], xmm3
	vextracti128 xmm13, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1056], xmm13
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
	vmovdqu XMMWORD PTR [rcx+624], xmm4
	vextracti128 xmm13, ymm4, 1
	vmovdqu XMMWORD PTR [rcx+880], xmm13
	vmovdqu XMMWORD PTR [rcx+688], xmm5
	vextracti128 xmm13, ymm5, 1
	vmovdqu XMMWORD PTR [rcx+944], xmm13
	vmovdqu XMMWORD PTR [rcx+752], xmm6
	vextracti128 xmm13, ymm6, 1
	vmovdqu XMMWORD PTR [rcx+1008], xmm13
	vmovdqu XMMWORD PTR [rcx+816], xmm7
	vextracti128 xmm13, ymm7, 1
	vmovdqu XMMWORD PTR [rcx+1072], xmm13
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
	vmovdqu XMMWORD PTR [rcx+656], xmm8
	vextracti128 xmm13, ymm8, 1
	vmovdqu XMMWORD PTR [rcx+912], xmm13
	vmovdqu XMMWORD PTR [rcx+720], xmm9
	vextracti128 xmm13, ymm9, 1
	vmovdqu XMMWORD PTR [rcx+976], xmm13
	vmovdqu XMMWORD PTR [rcx+784], xmm10
	vextracti128 xmm13, ymm10, 1
	vmovdqu XMMWORD PTR [rcx+1040], xmm13
	vmovdqu XMMWORD PTR [rcx+848], xmm11
	vextracti128 xmm13, ymm11, 1
	vmovdqu XMMWORD PTR [rcx+1104], xmm13
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
	vmovdqu XMMWORD PTR [rcx+640], xmm0
	vextracti128 xmm13, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+896], xmm13
	vmovdqu XMMWORD PTR [rcx+704], xmm1
	vextracti128 xmm13, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+960], xmm13
	vmovdqu XMMWORD PTR [rcx+768], xmm2
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1024], xmm13
	vmovdqu XMMWORD PTR [rcx+832], xmm3
	vextracti128 xmm13, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1088], xmm13
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 448
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
	mov rsi, rcx
	add rsi, 608
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 282f
284:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 284b
	jmp 283f
282:
283:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 285f
287:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 287b
	jmp 286f
285:
286:
	cmp rcx, rdx
	je 288f
290:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 290b
	jmp 289f
288:
289:
	vzeroupper
	mov rcx, r9
	mov edx, 0
	jmp 281f
280:
	cmp rdx, 128
	jb 291f
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
	mov r12, r9
	mov r9, rcx
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
	mov r9, r12
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 448
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
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
	mov rsi, r9
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 293f
295:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 295b
	jmp 294f
293:
294:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 296f
298:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 298b
	jmp 297f
296:
297:
	cmp rcx, rdx
	je 299f
2101:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 2101b
	jmp 2100f
299:
2100:
	vzeroupper
	mov rcx, r9
	mov edx, 0
	jmp 292f
291:
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
	mov r12, r9
	mov r9, rcx
	vmovdqu ymm8, YMMWORD PTR [r9+128]
	vmovdqu ymm9, YMMWORD PTR [r9+160]
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vbroadcasti128 ymm1, XMMWORD PTR [rdi+16]
	vbroadcasti128 ymm2, XMMWORD PTR [rdi+32]
	vbroadcasti128 ymm3, XMMWORD PTR [rdi+48]
	vpaddd ymm3, ymm3, ymm12
	mov r9, r12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 448
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
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
	mov rsi, r9
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 2102f
2104:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 2104b
	jmp 2103f
2102:
2103:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 2105f
2107:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 2107b
	jmp 2106f
2105:
2106:
	cmp rcx, rdx
	je 2108f
2110:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 2110b
	jmp 2109f
2108:
2109:
	vzeroupper
	mov rcx, r9
	mov edx, 0
292:
281:
243:
	jmp 222f
221:
	mov eax, 1
	mov DWORD PTR [r15+112], eax
	mov rdi, r15
	add rdi, 64
	mov rsi, r14
	mov rdx, r13
	mov rcx, r15
	add rcx, 128
	cmp rdx, 512
	jb 2111f
	mov QWORD PTR [rcx+392], r12
	mov QWORD PTR [rcx+400], r13
	mov QWORD PTR [rcx+408], r14
	mov QWORD PTR [rcx+416], rdx
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
	mov rdi, rcx
	add rdi, 320
	movabs rax, 1152921487695413247
	mov r8, QWORD PTR [rdi+24]
	and r8, rax
	movabs rax, 1152921487695413244
	mov r9, QWORD PTR [rdi+32]
	and r9, rax
	mov r10, r9
	shr r10, 2
	add r10, r9
	mov r11, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	mov rdi, rcx
	sub rdi, 64
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
	mov rdx, QWORD PTR [rcx+416]
	sub rdx, 512
	mov QWORD PTR [rcx+416], rdx
	cmp rdx, 512
	jb 2113f
2115:
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+448]
	adc rbx, QWORD PTR [rsi+456]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+464]
	adc rbx, QWORD PTR [rsi+472]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+480]
	adc rbx, QWORD PTR [rsi+488]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+496]
	adc rbx, QWORD PTR [rsi+504]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vmovdqu YMMWORD PTR [rcx+64], ymm14
	vmovdqu YMMWORD PTR [rcx+96], ymm15
	vmovdqu ymm15, YMMWORD PTR [rcx+128]
	add rsi, 512
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
	mov rdx, QWORD PTR [rcx+416]
	sub rdx, 512
	mov QWORD PTR [rcx+416], rdx
	cmp rdx, 512
	jae 2115b
	jmp 2114f
2113:
2114:
	mov rdx, QWORD PTR [rcx+416]
	sub rdx, 1
	cmp rdx, 256
	jb 2116f
	mov eax, 0
	mov eax, 0
	mov eax, 0
	mov eax, eax
	mov eax, eax
	cmp rdx, 448
	jb 2118f
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	mov rbp, QWORD PTR [rcx+416]
	add rbp, 512
	mov rdx, QWORD PTR [rcx+416]
	add rsi, 512
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	jmp 2119f
2118:
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+448]
	adc rbx, QWORD PTR [rsi+456]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+464]
	adc rbx, QWORD PTR [rsi+472]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+480]
	adc rbx, QWORD PTR [rsi+488]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+496]
	adc rbx, QWORD PTR [rsi+504]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
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
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	vmovdqu XMMWORD PTR [rcx+608], xmm0
	vextracti128 xmm13, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+864], xmm13
	vmovdqu XMMWORD PTR [rcx+672], xmm1
	vextracti128 xmm13, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+928], xmm13
	vmovdqu XMMWORD PTR [rcx+736], xmm2
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+992], xmm13
	vmovdqu XMMWORD PTR [rcx+800], xmm3
	vextracti128 xmm13, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1056], xmm13
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
	vmovdqu XMMWORD PTR [rcx+624], xmm4
	vextracti128 xmm13, ymm4, 1
	vmovdqu XMMWORD PTR [rcx+880], xmm13
	vmovdqu XMMWORD PTR [rcx+688], xmm5
	vextracti128 xmm13, ymm5, 1
	vmovdqu XMMWORD PTR [rcx+944], xmm13
	vmovdqu XMMWORD PTR [rcx+752], xmm6
	vextracti128 xmm13, ymm6, 1
	vmovdqu XMMWORD PTR [rcx+1008], xmm13
	vmovdqu XMMWORD PTR [rcx+816], xmm7
	vextracti128 xmm13, ymm7, 1
	vmovdqu XMMWORD PTR [rcx+1072], xmm13
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
	vmovdqu XMMWORD PTR [rcx+656], xmm8
	vextracti128 xmm13, ymm8, 1
	vmovdqu XMMWORD PTR [rcx+912], xmm13
	vmovdqu XMMWORD PTR [rcx+720], xmm9
	vextracti128 xmm13, ymm9, 1
	vmovdqu XMMWORD PTR [rcx+976], xmm13
	vmovdqu XMMWORD PTR [rcx+784], xmm10
	vextracti128 xmm13, ymm10, 1
	vmovdqu XMMWORD PTR [rcx+1040], xmm13
	vmovdqu XMMWORD PTR [rcx+848], xmm11
	vextracti128 xmm13, ymm11, 1
	vmovdqu XMMWORD PTR [rcx+1104], xmm13
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
	vmovdqu XMMWORD PTR [rcx+640], xmm0
	vextracti128 xmm13, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+896], xmm13
	vmovdqu XMMWORD PTR [rcx+704], xmm1
	vextracti128 xmm13, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+960], xmm13
	vmovdqu XMMWORD PTR [rcx+768], xmm2
	vextracti128 xmm13, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1024], xmm13
	vmovdqu XMMWORD PTR [rcx+832], xmm3
	vextracti128 xmm13, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1088], xmm13
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 512
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
	mov rsi, rcx
	add rsi, 608
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 2120f
2122:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 2122b
	jmp 2121f
2120:
2121:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 2123f
2125:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 2125b
	jmp 2124f
2123:
2124:
	cmp rcx, rdx
	je 2126f
2128:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 2128b
	jmp 2127f
2126:
2127:
	vzeroupper
	mov rcx, r9
	mov edx, 0
	mov eax, 0
	mov eax, 0
	mov eax, 0
	mov eax, 0
	mov eax, 0
	mov eax, eax
	mov eax, eax
2119:
	jmp 2117f
2116:
	cmp rdx, 128
	jb 2129f
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
	mov r12, r9
	mov r9, rcx
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
	mov r9, r12
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
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+448]
	adc rbx, QWORD PTR [rsi+456]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+464]
	adc rbx, QWORD PTR [rsi+472]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+480]
	adc rbx, QWORD PTR [rsi+488]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+496]
	adc rbx, QWORD PTR [rsi+504]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	vpshufd ymm5, ymm5, 147
	vpshufd ymm6, ymm6, 78
	vpshufd ymm7, ymm7, 57
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 512
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
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
	mov rsi, r9
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 2131f
2133:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 2133b
	jmp 2132f
2131:
2132:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 2134f
2136:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 2136b
	jmp 2135f
2134:
2135:
	cmp rcx, rdx
	je 2137f
2139:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 2139b
	jmp 2138f
2137:
2138:
	vzeroupper
	mov rcx, r9
	mov edx, 0
	jmp 2130f
2129:
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
	mov r12, r9
	mov r9, rcx
	vmovdqu ymm8, YMMWORD PTR [r9+128]
	vmovdqu ymm9, YMMWORD PTR [r9+160]
	vmovdqu ymm12, YMMWORD PTR [r9+224]
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vbroadcasti128 ymm1, XMMWORD PTR [rdi+16]
	vbroadcasti128 ymm2, XMMWORD PTR [rdi+32]
	vbroadcasti128 ymm3, XMMWORD PTR [rdi+48]
	vpaddd ymm3, ymm3, ymm12
	mov r9, r12
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm8
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 12
	vpsrld ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi]
	adc rbx, QWORD PTR [rsi+8]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+16]
	adc rbx, QWORD PTR [rsi+24]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+32]
	adc rbx, QWORD PTR [rsi+40]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+48]
	adc rbx, QWORD PTR [rsi+56]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+64]
	adc rbx, QWORD PTR [rsi+72]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+80]
	adc rbx, QWORD PTR [rsi+88]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+96]
	adc rbx, QWORD PTR [rsi+104]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+112]
	adc rbx, QWORD PTR [rsi+120]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+128]
	adc rbx, QWORD PTR [rsi+136]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+144]
	adc rbx, QWORD PTR [rsi+152]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+160]
	adc rbx, QWORD PTR [rsi+168]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+176]
	adc rbx, QWORD PTR [rsi+184]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+192]
	adc rbx, QWORD PTR [rsi+200]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+208]
	adc rbx, QWORD PTR [rsi+216]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+224]
	adc rbx, QWORD PTR [rsi+232]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+240]
	adc rbx, QWORD PTR [rsi+248]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+256]
	adc rbx, QWORD PTR [rsi+264]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+272]
	adc rbx, QWORD PTR [rsi+280]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+288]
	adc rbx, QWORD PTR [rsi+296]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+304]
	adc rbx, QWORD PTR [rsi+312]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+320]
	adc rbx, QWORD PTR [rsi+328]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+336]
	adc rbx, QWORD PTR [rsi+344]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+352]
	adc rbx, QWORD PTR [rsi+360]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+368]
	adc rbx, QWORD PTR [rsi+376]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+384]
	adc rbx, QWORD PTR [rsi+392]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+400]
	adc rbx, QWORD PTR [rsi+408]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+416]
	adc rbx, QWORD PTR [rsi+424]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+432]
	adc rbx, QWORD PTR [rsi+440]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+448]
	adc rbx, QWORD PTR [rsi+456]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+464]
	adc rbx, QWORD PTR [rsi+472]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
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
	add r11, QWORD PTR [rsi+480]
	adc rbx, QWORD PTR [rsi+488]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpaddd ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm9
	vpaddd ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vpslld ymm10, ymm1, 7
	vpsrld ymm1, ymm1, 25
	vpor ymm1, ymm1, ymm10
	add r11, QWORD PTR [rsi+496]
	adc rbx, QWORD PTR [rsi+504]
	adc rbp, 1
	mov rax, r11
	mul r8
	mov r12, rax
	mov r13, rdx
	mov rax, rbx
	mul r10
	add r12, rax
	adc r13, rdx
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r10
	add r14, rax
	adc r15, rdx
	mov rax, rbp
	mul r8
	add r14, r13
	adc r15, rax
	mov r11, r12
	mov rbx, r14
	mov rbp, r15
	and rbp, 3
	mov rax, r15
	sub rax, rbp
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	vpshufd ymm1, ymm1, 147
	vpshufd ymm2, ymm2, 78
	vpshufd ymm3, ymm3, 57
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rcx+320], r11
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rbp
	mov rbx, rsi
	add rbx, 512
	mov rbp, QWORD PTR [rcx+416]
	mov r12, QWORD PTR [rcx+392]
	mov r13, QWORD PTR [rcx+400]
	mov r14, QWORD PTR [rcx+408]
	mov r15, rcx
	sub r15, 128
	mov r9, rcx
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
	mov rsi, r9
	mov rdx, rbp
	test rdx, rdx
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 2140f
2142:
	vmovdqu ymm0, YMMWORD PTR [rbx+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rbx+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 2142b
	jmp 2141f
2140:
2141:
	mov rdi, rbx
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 2143f
2145:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 2145b
	jmp 2144f
2143:
2144:
	cmp rcx, rdx
	je 2146f
2148:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 2148b
	jmp 2147f
2146:
2147:
	vzeroupper
	mov rcx, r9
	mov edx, 0
2130:
2117:
	jmp 2112f
2111:
	mov rbx, r14
	mov rbp, r13
2112:
222:
	test rdx, rdx
	je 2149f
	mov r8, rsi
	call {vg_chacha20_xor_avx512vl}
	jmp 2150f
2149:
	mov rsi, rcx
2150:
	jmp 220f
219:
	mov rsi, r15
	add rsi, 736
	mov rdx, r13
	mov ecx, 0
	mov rax, rdx
	shr rax, 5
	je 2151f
2153:
	vmovdqu ymm0, YMMWORD PTR [r14+rcx*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [r14+rcx*1], ymm0
	add rcx, 32
	sub rax, 1
	jne 2153b
	jmp 2152f
2151:
2152:
	mov rdi, r14
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 2154f
2156:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 2156b
	jmp 2155f
2154:
2155:
	cmp rcx, rdx
	je 2157f
2159:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 2159b
	jmp 2158f
2157:
2158:
	mov rsi, r15
	add rsi, 128
	mov rbx, r14
	mov rbp, r13
220:
	mov r15, rsi
	sub r15, 128
	cmp r13, 449
	jb 2160f
	mov edx, 512
	jmp 2161f
2160:
	mov rdx, r13
2161:
	add rdx, 64
	vpxor ymm0, ymm0, ymm0
	mov ecx, 0
2162:
	vmovdqu YMMWORD PTR [r15+rcx*1+672], ymm0
	add rcx, 32
	cmp rcx, rdx
	jb 2162b
	vzeroupper
	mov rdi, r15
	add rdi, 448
	mov rsi, rbx
	mov rdx, rbp
	shr rdx, 4
	je 2163f
	call {vg_poly1305_blocks_avx2}
	mov r15, rdi
	sub r15, 448
	jmp 2164f
2163:
2164:
	mov rdx, rbp
	and rdx, 15
	jne 2165f
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 592
	mov edx, 1
	call {vg_poly1305_blocks_avx2}
	mov r15, rdi
	sub r15, 448
2166:
	mov rdi, r15
	add rdi, 448
	mov esi, 0
	mov rdx, r12
	call {vg_poly1305_finalize_scratch}
	mov r15, rdi
	sub r15, 448
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r13, QWORD PTR [r15+16]
	mov r14, QWORD PTR [r15+24]
	mov r12, QWORD PTR [r15+40]
	mov r15, QWORD PTR [r15+32]
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	lea rsp, [rsp+1728]
	ret
27:
	jne 211f
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	mov eax, 0
	add rax, 1
	jmp 212f
211:
212:
	mov rsi, rbp
	sub rsi, rdx
	add rsi, rbx
	xor r9d, r9d
	cmp rdx, 8
	jb 213f
	mov rax, QWORD PTR [rsi]
	add rsi, 8
	sub rdx, 8
	je 215f
217:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 217b
	jmp 216f
215:
216:
	jmp 214f
213:
218:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 218b
	mov rax, r9
	xor r9d, r9d
214:
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 576
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], r9
	mov edx, 1
	call {vg_poly1305_blocks_avx2}
	mov r15, rdi
	sub r15, 448
	jmp 28b
2165:
	mov rsi, rbp
	sub rsi, rdx
	add rsi, rbx
	xor r9d, r9d
	cmp rdx, 8
	jb 2167f
	mov rax, QWORD PTR [rsi]
	add rsi, 8
	sub rdx, 8
	je 2169f
2171:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 2171b
	jmp 2170f
2169:
2170:
	jmp 2168f
2167:
2172:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 2172b
	mov rax, r9
	xor r9d, r9d
2168:
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 576
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], r9
	mov edx, 2
	call {vg_poly1305_blocks_avx2}
	mov r15, rdi
	sub r15, 448
	jmp 2166b
	.p2align 6
