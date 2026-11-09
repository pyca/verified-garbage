// The functions of `src/internal/vg_mldsa65_verify_with_cache_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_verify_with_cache_avx512:
	mov QWORD PTR [rcx+840], rbx
	mov QWORD PTR [rcx+848], rbp
	mov QWORD PTR [rcx+856], r12
	mov QWORD PTR [rcx+864], r13
	mov QWORD PTR [rcx+872], r14
	mov QWORD PTR [rcx+880], r15
	mov rbx, rcx
	mov rbp, rdi
	mov r12, rsi
	mov r13, rdx
	mov r15d, 1
	mov QWORD PTR [rcx+888], r8
	mov rdi, r13
	add rdi, 3248
	mov esi, 61
	mov edx, 55
	mov rcx, rbx
	add rcx, 8192
	mov r8d, 1536
	call {vg_mldsa_hint_bit_unpack}
	mov r15d, eax
	test r15d, r15d
	jne 20f
	jmp 21f
20:
	mov rdi, r13
	add rdi, 48
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 16384
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 688
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 17408
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 1328
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 18432
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 1968
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 19456
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 2608
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 20480
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20480
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 22f
	jmp 23f
22:
	mov rdi, rbx
	add rdi, 896
	mov rsi, rbp
	add rsi, 0
	mov ecx, 32
24:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rdi, 1
	add rsi, 1
	sub rcx, 1
	jne 24b
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbp
	add rsi, 0
	mov ecx, 32
25:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rdi, 1
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov rdi, rbx
	add rdi, 2594
	mov rsi, rbp
	add rsi, 0
	mov ecx, 32
26:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rdi, 1
	add rsi, 1
	sub rcx, 1
	jne 26b
	mov rdi, rbx
	add rdi, 2628
	mov rsi, rbp
	add rsi, 0
	mov ecx, 32
27:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rdi, 1
	add rsi, 1
	sub rcx, 1
	jne 27b
	mov rdi, rbx
	add rdi, 2662
	mov rsi, rbp
	add rsi, 0
	mov ecx, 32
28:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rdi, 1
	add rsi, 1
	sub rcx, 1
	jne 28b
	mov eax, 0
	mov BYTE PTR [rbx+2592], al
	mov eax, 0
	mov BYTE PTR [rbx+2593], al
	mov eax, 1
	mov BYTE PTR [rbx+2626], al
	mov eax, 0
	mov BYTE PTR [rbx+2627], al
	mov eax, 2
	mov BYTE PTR [rbx+2660], al
	mov eax, 0
	mov BYTE PTR [rbx+2661], al
	mov eax, 3
	mov BYTE PTR [rbx+2694], al
	mov eax, 0
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 77824
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 28672
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
29:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 29b
	mov eax, 4
	mov BYTE PTR [rbx+2592], al
	mov eax, 0
	mov BYTE PTR [rbx+2593], al
	mov eax, 0
	mov BYTE PTR [rbx+2626], al
	mov eax, 1
	mov BYTE PTR [rbx+2627], al
	mov eax, 1
	mov BYTE PTR [rbx+2660], al
	mov eax, 1
	mov BYTE PTR [rbx+2661], al
	mov eax, 2
	mov BYTE PTR [rbx+2694], al
	mov eax, 1
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 77824
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 32768
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
210:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 210b
	mov eax, 3
	mov BYTE PTR [rbx+2592], al
	mov eax, 1
	mov BYTE PTR [rbx+2593], al
	mov eax, 4
	mov BYTE PTR [rbx+2626], al
	mov eax, 1
	mov BYTE PTR [rbx+2627], al
	mov eax, 0
	mov BYTE PTR [rbx+2660], al
	mov eax, 2
	mov BYTE PTR [rbx+2661], al
	mov eax, 1
	mov BYTE PTR [rbx+2694], al
	mov eax, 2
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 77824
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 36864
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
211:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 211b
	mov eax, 2
	mov BYTE PTR [rbx+2592], al
	mov eax, 2
	mov BYTE PTR [rbx+2593], al
	mov eax, 3
	mov BYTE PTR [rbx+2626], al
	mov eax, 2
	mov BYTE PTR [rbx+2627], al
	mov eax, 4
	mov BYTE PTR [rbx+2660], al
	mov eax, 2
	mov BYTE PTR [rbx+2661], al
	mov eax, 0
	mov BYTE PTR [rbx+2694], al
	mov eax, 3
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 77824
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 40960
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
212:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 212b
	mov eax, 1
	mov BYTE PTR [rbx+2592], al
	mov eax, 3
	mov BYTE PTR [rbx+2593], al
	mov eax, 2
	mov BYTE PTR [rbx+2626], al
	mov eax, 3
	mov BYTE PTR [rbx+2627], al
	mov eax, 3
	mov BYTE PTR [rbx+2660], al
	mov eax, 3
	mov BYTE PTR [rbx+2661], al
	mov eax, 4
	mov BYTE PTR [rbx+2694], al
	mov eax, 3
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 77824
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 45056
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
213:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 213b
	mov eax, 0
	mov BYTE PTR [rbx+2592], al
	mov eax, 4
	mov BYTE PTR [rbx+2593], al
	mov eax, 1
	mov BYTE PTR [rbx+2626], al
	mov eax, 4
	mov BYTE PTR [rbx+2627], al
	mov eax, 2
	mov BYTE PTR [rbx+2660], al
	mov eax, 4
	mov BYTE PTR [rbx+2661], al
	mov eax, 3
	mov BYTE PTR [rbx+2694], al
	mov eax, 4
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 77824
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 49152
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
214:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 214b
	mov eax, 4
	mov BYTE PTR [rbx+2592], al
	mov eax, 4
	mov BYTE PTR [rbx+2593], al
	mov eax, 0
	mov BYTE PTR [rbx+2626], al
	mov eax, 5
	mov BYTE PTR [rbx+2627], al
	mov eax, 1
	mov BYTE PTR [rbx+2660], al
	mov eax, 5
	mov BYTE PTR [rbx+2661], al
	mov eax, 2
	mov BYTE PTR [rbx+2694], al
	mov eax, 5
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 77824
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 53248
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
215:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 215b
	mov eax, 1
	mov BYTE PTR [rbx+2592], al
	mov eax, 5
	mov BYTE PTR [rbx+2593], al
	mov eax, 2
	mov BYTE PTR [rbx+2626], al
	mov eax, 5
	mov BYTE PTR [rbx+2627], al
	mov eax, 3
	mov BYTE PTR [rbx+2660], al
	mov eax, 5
	mov BYTE PTR [rbx+2661], al
	mov eax, 4
	mov BYTE PTR [rbx+2694], al
	mov eax, 5
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 55296
	mov rdx, rbx
	add rdx, 77824
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 55296
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
216:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 216b
	mov rdi, r13
	add rdi, 0
	mov esi, 48
	mov edx, 49
	mov rcx, rbx
	add rcx, 23552
	mov r8, rbx
	add r8, 4096
	call {vg_mldsa_sample_in_ball}
	and r15d, eax
	mov rdi, rbx
	add rdi, 23552
	mov ecx, 64
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
217:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 217b
	mov rdi, rbx
	add rdi, 16384
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 17408
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 30720
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 31744
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rax, QWORD PTR [rbx+888]
	test rax, rax
	jne 218f
	mov rdi, rbp
	add rdi, 32
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	jmp 219f
218:
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbp
	add rsi, 1952
	mov ecx, 128
220:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 220b
219:
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1024
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 34816
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 35840
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 37888
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rax, QWORD PTR [rbx+888]
	test rax, rax
	jne 221f
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	jmp 222f
221:
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbp
	add rsi, 2976
	mov ecx, 128
223:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 223b
222:
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1152
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 39936
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 41984
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rax, QWORD PTR [rbx+888]
	test rax, rax
	jne 224f
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	jmp 225f
224:
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbp
	add rsi, 4000
	mov ecx, 128
226:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 226b
225:
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 10240
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1280
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 44032
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 46080
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 48128
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rax, QWORD PTR [rbx+888]
	test rax, rax
	jne 227f
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	jmp 228f
227:
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbp
	add rsi, 5024
	mov ecx, 128
229:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 229b
228:
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 11264
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1408
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 50176
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 52224
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rax, QWORD PTR [rbx+888]
	test rax, rax
	jne 230f
	mov rdi, rbp
	add rdi, 1312
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	jmp 231f
230:
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbp
	add rsi, 6048
	mov ecx, 128
232:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 232b
231:
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 12288
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1536
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 54272
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 55296
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 56320
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 57344
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 58368
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rax, QWORD PTR [rbx+888]
	test rax, rax
	jne 233f
	mov rdi, rbp
	add rdi, 1632
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	jmp 234f
233:
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbp
	add rsi, 7072
	mov ecx, 128
235:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 235b
234:
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 13312
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1664
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, r12
	add rcx, 0
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 64
	mov rcx, rbx
	add rcx, 1024
	mov r8d, 768
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 16
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 2048
	mov r8d, 48
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 2048
	mov rdi, r13
	add rdi, 0
	mov ecx, 48
	mov edx, 0
236:
	movzx eax, BYTE PTR [rsi]
	movzx r8d, BYTE PTR [rdi]
	xor rax, r8
	or rdx, rax
	add rsi, 1
	add rdi, 1
	sub rcx, 1
	jne 236b
	sub rdx, 1
	sbb rax, rax
	and r15d, eax
23:
21:
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6
