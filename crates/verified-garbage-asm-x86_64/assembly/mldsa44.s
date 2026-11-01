// The functions of `src/mldsa44.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_keygen_avx2:
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
	mov eax, 4
	mov BYTE PTR [rbx+896], al
	mov eax, 4
	mov BYTE PTR [rbx+897], al
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
	mov rcx, rbp
	add rcx, 0
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 32
	mov rcx, rbx
	add rcx, 896
	mov r8d, 2
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 34
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 1024
	mov r8d, 128
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rdi, rbx
	add rdi, 1216
	mov rsi, rbx
	add rsi, 1056
	mov ecx, 8
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 21b
	mov eax, 0
	mov BYTE PTR [rbx+1281], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 22b
	mov rdi, rbx
	add rdi, 1442
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
23:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 23b
	mov rdi, rbx
	add rdi, 1476
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
24:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 24b
	mov rdi, rbx
	add rdi, 1510
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
25:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 25b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 0
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 0
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 0
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 0
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 4096
	mov ecx, 1024
26:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 26b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 1
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 8192
	mov ecx, 1024
27:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 27b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 2
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 2
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 2
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 2
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 12288
	mov ecx, 1024
28:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 28b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 3
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 16384
	mov ecx, 1024
29:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 29b
	mov eax, 0
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 20480
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 20480
	mov ecx, 256
210:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 210b
	mov eax, 1
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 21504
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 21504
	mov ecx, 256
211:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 211b
	mov eax, 2
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 22528
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 22528
	mov ecx, 256
212:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 212b
	mov eax, 3
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 23552
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 23552
	mov ecx, 256
213:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 213b
	mov eax, 4
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 24576
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 24576
	mov ecx, 256
214:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 214b
	mov eax, 5
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 25600
	mov ecx, 256
215:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 215b
	mov eax, 6
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 26624
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 26624
	mov ecx, 256
216:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 216b
	mov eax, 7
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 27648
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 27648
	mov ecx, 256
217:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 217b
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 218b
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
219:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 219b
	mov rdi, r13
	add rdi, 32
	mov rsi, rbx
	add rsi, 1120
	mov ecx, 4
220:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 220b
	mov rdi, rbx
	add rdi, 20480
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 128
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 21504
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 224
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 320
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 416
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 512
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 25600
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 608
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 704
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 800
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 6144
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 7168
	mov rdx, rbx
	add rdx, 23552
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 1023
	mov rdx, r12
	add rdx, 32
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 896
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 9216
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 10240
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 11264
	mov rdx, rbx
	add rdx, 23552
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 1023
	mov rdx, r12
	add rdx, 352
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1312
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 13312
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 14336
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 15360
	mov rdx, rbx
	add rdx, 23552
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 26624
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 1023
	mov rdx, r12
	add rdx, 672
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1728
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 17408
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 18432
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 19456
	mov rdx, rbx
	add rdx, 23552
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 27648
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 1023
	mov rdx, r12
	add rdx, 992
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2144
	mov r8d, 416
	call {vg_mldsa_bit_pack}
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
	mov r8d, 1312
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 88
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, r13
	add rcx, 64
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6

vg_mldsa44_sign_avx2:
	mov QWORD PTR [r8+840], rbx
	mov QWORD PTR [r8+848], rbp
	mov QWORD PTR [r8+856], r12
	mov QWORD PTR [r8+864], r13
	mov QWORD PTR [r8+872], r14
	mov QWORD PTR [r8+880], r15
	mov rbx, r8
	mov rbp, rdi
	mov r12, rsi
	mov r13, rdx
	mov r14, rcx
	mov r15d, 1
	mov rdi, rbx
	add rdi, 912
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 21b
	mov rdi, rbx
	add rdi, 1186
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 22b
	mov rdi, rbx
	add rdi, 1220
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
23:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 23b
	mov rdi, rbx
	add rdi, 1254
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
24:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 24b
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 0
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 0
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 0
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 0
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 1
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 1
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 1
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 1
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 2
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 2
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 2
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 2
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 3
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 3
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 3
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 3
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	test r15d, r15d
	jne 25f
	jmp 26f
25:
	mov rdi, rbp
	add rdi, 128
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 26624
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 27648
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 28672
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 29696
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 30720
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 31744
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 32768
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 33792
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 896
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 34816
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1312
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 35840
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1728
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 36864
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2144
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 37888
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
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
	mov rcx, rbp
	add rcx, 32
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 32
	mov rcx, r13
	add rcx, 0
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 64
	mov rcx, r12
	add rcx, 0
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 128
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 960
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov eax, 0
	mov QWORD PTR [rbx+896], rax
	mov eax, 814
	mov QWORD PTR [rbx+888], rax
27:
	mov rdi, rbx
	add rdi, 1296
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
28:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 28b
	mov rax, QWORD PTR [rbx+896]
	add rax, 0
	mov BYTE PTR [rbx+1360], al
	shr rax, 8
	mov BYTE PTR [rbx+1361], al
	mov rdi, rbx
	add rdi, 1362
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
29:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 29b
	mov rax, QWORD PTR [rbx+896]
	add rax, 1
	mov BYTE PTR [rbx+1426], al
	shr rax, 8
	mov BYTE PTR [rbx+1427], al
	mov rdi, rbx
	add rdi, 1428
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
210:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 210b
	mov rax, QWORD PTR [rbx+896]
	add rax, 2
	mov BYTE PTR [rbx+1492], al
	shr rax, 8
	mov BYTE PTR [rbx+1493], al
	mov rdi, rbx
	add rdi, 1494
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
211:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 211b
	mov rax, QWORD PTR [rbx+896]
	add rax, 3
	mov BYTE PTR [rbx+1558], al
	shr rax, 8
	mov BYTE PTR [rbx+1559], al
	mov rdi, rbx
	add rdi, 1296
	mov esi, 131072
	mov rdx, rbx
	add rdx, 14336
	mov rcx, rbx
	add rcx, 55296
	call {vg_mldsa_expand_mask_poly4_avx2}
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 14336
	mov ecx, 128
212:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 212b
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 15360
	mov ecx, 128
213:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 213b
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 16384
	mov ecx, 128
214:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 214b
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 17408
	mov ecx, 128
215:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 215b
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse4_avx2}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse4_avx2}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse4_avx2}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse4_avx2}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 95232
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 43
	mov rdx, rbx
	add rdx, 2048
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 95232
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 43
	mov rdx, rbx
	add rdx, 2240
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 95232
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 43
	mov rdx, rbx
	add rdx, 2432
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 25600
	mov esi, 95232
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 43
	mov rdx, rbx
	add rdx, 2624
	mov ecx, 192
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
	add rcx, 2048
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
	add rcx, 1040
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, rbx
	add rdi, 1040
	mov esi, 32
	mov edx, 39
	mov rcx, rbx
	add rcx, 5120
	mov r8, rbx
	add r8, 3072
	call {vg_mldsa_sample_in_ball}
	test eax, eax
	jne 216f
	mov r15d, 0
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
	jmp 217f
216:
	mov rdi, rbx
	add rdi, 5120
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov r15d, 1
	mov eax, 0
	mov QWORD PTR [rbx+904], rax
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 26624
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 14336
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 14336
	mov esi, 130994
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 218f
	jmp 219f
218:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 27648
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 15360
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 15360
	mov esi, 130994
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 220f
	jmp 221f
220:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 28672
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 16384
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 130994
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 222f
	jmp 223f
222:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 29696
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 17408
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 130994
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 224f
	jmp 225f
224:
225:
223:
221:
219:
	test r15d, r15d
	jne 226f
	jmp 227f
226:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 95232
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 95154
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 228f
	jmp 229f
228:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 95232
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 95154
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 230f
	jmp 231f
230:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 32768
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 95232
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 95154
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 232f
	jmp 233f
232:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 33792
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 25600
	mov esi, 95232
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 95154
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 234f
	jmp 235f
234:
235:
233:
231:
229:
	test r15d, r15d
	jne 236f
	jmp 237f
236:
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 34816
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 95232
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 22528
	mov ecx, 128
238:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 238b
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 22528
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 22528
	mov edx, 95232
	mov rcx, rbx
	add rcx, 10240
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 35840
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 95232
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 23552
	mov ecx, 128
239:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 239b
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 23552
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 23552
	mov edx, 95232
	mov rcx, rbx
	add rcx, 11264
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 36864
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 95232
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 24576
	mov ecx, 128
240:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 240b
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 24576
	mov edx, 95232
	mov rcx, rbx
	add rcx, 12288
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 37888
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 95232
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 25600
	mov ecx, 128
241:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 241b
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 25600
	mov edx, 95232
	mov rcx, rbx
	add rcx, 13312
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov eax, DWORD PTR [rbx+904]
	sub rax, 81
	shr rax, 63
	and r15d, eax
237:
227:
	test r15d, r15d
	jne 242f
	mov rax, QWORD PTR [rbx+896]
	add rax, 4
	mov QWORD PTR [rbx+896], rax
	jmp 243f
242:
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
243:
217:
	mov rax, QWORD PTR [rbx+888]
	sub rax, 1
	mov QWORD PTR [rbx+888], rax
	jne 27b
	test r15d, r15d
	jne 244f
	jmp 245f
244:
	mov rdi, r14
	add rdi, 0
	mov rsi, rbx
	add rsi, 1040
	mov ecx, 4
246:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 246b
	mov rdi, rbx
	add rdi, 14336
	mov esi, 131071
	mov edx, 131072
	mov rcx, r14
	add rcx, 32
	mov r8d, 576
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 15360
	mov esi, 131071
	mov edx, 131072
	mov rcx, r14
	add rcx, 608
	mov r8d, 576
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 131071
	mov edx, 131072
	mov rcx, r14
	add rcx, 1184
	mov r8d, 576
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 131071
	mov edx, 131072
	mov rcx, r14
	add rcx, 1760
	mov r8d, 576
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 10240
	mov esi, 1024
	mov edx, 80
	mov rcx, r14
	add rcx, 2336
	mov r8d, 84
	call {vg_mldsa_hint_bit_pack}
245:
26:
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6

vg_mldsa44_sign_message_avx2:
	cmp r8, 256
	jb 20f
	mov eax, 2
	jmp 21f
20:
	mov r10, QWORD PTR [rsp+8]
	mov r11, QWORD PTR [rsp+16]
	mov eax, 0
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r10
	push r9
	push r11
	push rax
	mov BYTE PTR [rsp+1], r8b
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 78024
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 78664
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 78664
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	call {vg_mldsa44_sign_avx2}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
21:
	ret
	.p2align 6

vg_mldsa44_verify_avx2:
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
	mov rdi, r13
	add rdi, 2336
	mov esi, 84
	mov edx, 80
	mov rcx, rbx
	add rcx, 8192
	mov r8d, 1024
	call {vg_mldsa_hint_bit_unpack}
	mov r15d, eax
	test r15d, r15d
	jne 20f
	jmp 21f
20:
	mov rdi, r13
	add rdi, 32
	mov esi, 576
	mov edx, 131071
	mov ecx, 131072
	mov r8, rbx
	add r8, 16384
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 130994
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 608
	mov esi, 576
	mov edx, 131071
	mov ecx, 131072
	mov r8, rbx
	add r8, 17408
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 130994
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 1184
	mov esi, 576
	mov edx, 131071
	mov ecx, 131072
	mov r8, rbx
	add r8, 18432
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 130994
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 1760
	mov esi, 576
	mov edx, 131071
	mov ecx, 131072
	mov r8, rbx
	add r8, 19456
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 130994
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
	add rdx, 61440
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	mov eax, 0
	mov BYTE PTR [rbx+2592], al
	mov eax, 1
	mov BYTE PTR [rbx+2593], al
	mov eax, 1
	mov BYTE PTR [rbx+2626], al
	mov eax, 1
	mov BYTE PTR [rbx+2627], al
	mov eax, 2
	mov BYTE PTR [rbx+2660], al
	mov eax, 1
	mov BYTE PTR [rbx+2661], al
	mov eax, 3
	mov BYTE PTR [rbx+2694], al
	mov eax, 1
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	mov eax, 0
	mov BYTE PTR [rbx+2592], al
	mov eax, 2
	mov BYTE PTR [rbx+2593], al
	mov eax, 1
	mov BYTE PTR [rbx+2626], al
	mov eax, 2
	mov BYTE PTR [rbx+2627], al
	mov eax, 2
	mov BYTE PTR [rbx+2660], al
	mov eax, 2
	mov BYTE PTR [rbx+2661], al
	mov eax, 3
	mov BYTE PTR [rbx+2694], al
	mov eax, 2
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	mov eax, 0
	mov BYTE PTR [rbx+2592], al
	mov eax, 3
	mov BYTE PTR [rbx+2593], al
	mov eax, 1
	mov BYTE PTR [rbx+2626], al
	mov eax, 3
	mov BYTE PTR [rbx+2627], al
	mov eax, 2
	mov BYTE PTR [rbx+2660], al
	mov eax, 3
	mov BYTE PTR [rbx+2661], al
	mov eax, 3
	mov BYTE PTR [rbx+2694], al
	mov eax, 3
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	mov rdi, r13
	add rdi, 0
	mov esi, 32
	mov edx, 39
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
213:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 213b
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
	mov edx, 95232
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 43
	mov rdx, rbx
	add rdx, 1024
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 34816
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 35840
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
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
	mov edx, 95232
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 43
	mov rdx, rbx
	add rdx, 1216
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 37888
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 39936
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
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
	mov edx, 95232
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 43
	mov rdx, rbx
	add rdx, 1408
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 41984
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 44032
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
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
	mov edx, 95232
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 43
	mov rdx, rbx
	add rdx, 1600
	mov ecx, 192
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
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 2048
	mov rdi, r13
	add rdi, 0
	mov ecx, 32
	mov edx, 0
214:
	movzx eax, BYTE PTR [rsi]
	movzx r8d, BYTE PTR [rdi]
	xor rax, r8
	or rdx, rax
	add rsi, 1
	add rdi, 1
	sub rcx, 1
	jne 214b
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

vg_mldsa44_verify_message_cached_avx2:
	cmp r8, 256
	jb 20f
	mov eax, 2
	jmp 21f
20:
	mov r11, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [rsp+16]
	mov eax, 0
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push r10
	push r11
	push rax
	mov BYTE PTR [rsp+1], r8b
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 78024
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 78664
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 78664
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	call {vg_mldsa44_verify_avx2}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
21:
	ret
	.p2align 6

vg_mldsa44_keygen:
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
	mov eax, 4
	mov BYTE PTR [rbx+896], al
	mov eax, 4
	mov BYTE PTR [rbx+897], al
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
	mov rcx, rbp
	add rcx, 0
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 32
	mov rcx, rbx
	add rcx, 896
	mov r8d, 2
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 34
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 1024
	mov r8d, 128
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rdi, rbx
	add rdi, 1216
	mov rsi, rbx
	add rsi, 1056
	mov ecx, 8
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 21b
	mov eax, 0
	mov BYTE PTR [rbx+1281], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 22b
	mov rdi, rbx
	add rdi, 1442
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
23:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 23b
	mov rdi, rbx
	add rdi, 1476
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
24:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 24b
	mov rdi, rbx
	add rdi, 1510
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
25:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 25b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 0
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 0
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 0
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 0
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 4096
	mov ecx, 1024
26:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 26b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 1
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 8192
	mov ecx, 1024
27:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 27b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 2
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 2
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 2
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 2
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 12288
	mov ecx, 1024
28:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 28b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 3
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 16384
	mov ecx, 1024
29:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 29b
	mov eax, 0
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 20480
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 20480
	mov ecx, 256
210:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 210b
	mov eax, 1
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 21504
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 21504
	mov ecx, 256
211:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 211b
	mov eax, 2
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 22528
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 22528
	mov ecx, 256
212:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 212b
	mov eax, 3
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 23552
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 23552
	mov ecx, 256
213:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 213b
	mov eax, 4
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 24576
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 24576
	mov ecx, 256
214:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 214b
	mov eax, 5
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 25600
	mov ecx, 256
215:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 215b
	mov eax, 6
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 26624
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 26624
	mov ecx, 256
216:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 216b
	mov eax, 7
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 27648
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 27648
	mov ecx, 256
217:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 217b
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 218b
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
219:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 219b
	mov rdi, r13
	add rdi, 32
	mov rsi, rbx
	add rsi, 1120
	mov ecx, 4
220:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 220b
	mov rdi, rbx
	add rdi, 20480
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 128
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 21504
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 224
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 320
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 416
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 512
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 25600
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 608
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 704
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 800
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 6144
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 7168
	mov rdx, rbx
	add rdx, 23552
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 1023
	mov rdx, r12
	add rdx, 32
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 896
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 9216
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 10240
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 11264
	mov rdx, rbx
	add rdx, 23552
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 1023
	mov rdx, r12
	add rdx, 352
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1312
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 13312
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 14336
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 15360
	mov rdx, rbx
	add rdx, 23552
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 26624
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 1023
	mov rdx, r12
	add rdx, 672
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1728
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 17408
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 18432
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 19456
	mov rdx, rbx
	add rdx, 23552
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 27648
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 1023
	mov rdx, r12
	add rdx, 992
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2144
	mov r8d, 416
	call {vg_mldsa_bit_pack}
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
	mov r8d, 1312
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 88
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, r13
	add rcx, 64
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6

vg_mldsa44_sign:
	mov QWORD PTR [r8+840], rbx
	mov QWORD PTR [r8+848], rbp
	mov QWORD PTR [r8+856], r12
	mov QWORD PTR [r8+864], r13
	mov QWORD PTR [r8+872], r14
	mov QWORD PTR [r8+880], r15
	mov rbx, r8
	mov rbp, rdi
	mov r12, rsi
	mov r13, rdx
	mov r14, rcx
	mov r15d, 1
	mov rdi, rbx
	add rdi, 912
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 21b
	mov rdi, rbx
	add rdi, 1186
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 22b
	mov rdi, rbx
	add rdi, 1220
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
23:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 23b
	mov rdi, rbx
	add rdi, 1254
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
24:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 24b
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 0
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 0
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 0
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 0
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 1
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 1
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 1
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 1
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 2
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 2
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 2
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 2
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 3
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 3
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 3
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 3
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	test r15d, r15d
	jne 25f
	jmp 26f
25:
	mov rdi, rbp
	add rdi, 128
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 26624
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 27648
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 28672
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 29696
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 30720
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 31744
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 32768
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 33792
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 896
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 34816
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1312
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 35840
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1728
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 36864
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2144
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 37888
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
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
	mov rcx, rbp
	add rcx, 32
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 32
	mov rcx, r13
	add rcx, 0
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 64
	mov rcx, r12
	add rcx, 0
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 128
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 960
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov eax, 0
	mov QWORD PTR [rbx+896], rax
	mov eax, 814
	mov QWORD PTR [rbx+888], rax
27:
	mov rdi, rbx
	add rdi, 1296
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
28:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 28b
	mov rax, QWORD PTR [rbx+896]
	add rax, 0
	mov BYTE PTR [rbx+1360], al
	shr rax, 8
	mov BYTE PTR [rbx+1361], al
	mov rdi, rbx
	add rdi, 1362
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
29:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 29b
	mov rax, QWORD PTR [rbx+896]
	add rax, 1
	mov BYTE PTR [rbx+1426], al
	shr rax, 8
	mov BYTE PTR [rbx+1427], al
	mov rdi, rbx
	add rdi, 1428
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
210:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 210b
	mov rax, QWORD PTR [rbx+896]
	add rax, 2
	mov BYTE PTR [rbx+1492], al
	shr rax, 8
	mov BYTE PTR [rbx+1493], al
	mov rdi, rbx
	add rdi, 1494
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
211:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 211b
	mov rax, QWORD PTR [rbx+896]
	add rax, 3
	mov BYTE PTR [rbx+1558], al
	shr rax, 8
	mov BYTE PTR [rbx+1559], al
	mov rdi, rbx
	add rdi, 1296
	mov esi, 131072
	mov rdx, rbx
	add rdx, 14336
	mov rcx, rbx
	add rcx, 55296
	call {vg_mldsa_expand_mask_poly4}
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 14336
	mov ecx, 128
212:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 212b
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 15360
	mov ecx, 128
213:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 213b
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 16384
	mov ecx, 128
214:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 214b
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 17408
	mov ecx, 128
215:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 215b
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse4}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse4}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse4}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse4}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 95232
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 43
	mov rdx, rbx
	add rdx, 2048
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 95232
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 43
	mov rdx, rbx
	add rdx, 2240
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 95232
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 43
	mov rdx, rbx
	add rdx, 2432
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 25600
	mov esi, 95232
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 43
	mov rdx, rbx
	add rdx, 2624
	mov ecx, 192
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
	add rcx, 2048
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
	add rcx, 1040
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, rbx
	add rdi, 1040
	mov esi, 32
	mov edx, 39
	mov rcx, rbx
	add rcx, 5120
	mov r8, rbx
	add r8, 3072
	call {vg_mldsa_sample_in_ball}
	test eax, eax
	jne 216f
	mov r15d, 0
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
	jmp 217f
216:
	mov rdi, rbx
	add rdi, 5120
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov r15d, 1
	mov eax, 0
	mov QWORD PTR [rbx+904], rax
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 26624
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 14336
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 14336
	mov esi, 130994
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 218f
	jmp 219f
218:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 27648
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 15360
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 15360
	mov esi, 130994
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 220f
	jmp 221f
220:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 28672
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 16384
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 130994
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 222f
	jmp 223f
222:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 29696
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 17408
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 130994
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 224f
	jmp 225f
224:
225:
223:
221:
219:
	test r15d, r15d
	jne 226f
	jmp 227f
226:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 30720
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 95232
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 95154
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 228f
	jmp 229f
228:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 31744
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 95232
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 95154
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 230f
	jmp 231f
230:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 32768
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 95232
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 95154
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 232f
	jmp 233f
232:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 33792
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 25600
	mov esi, 95232
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 95154
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 234f
	jmp 235f
234:
235:
233:
231:
229:
	test r15d, r15d
	jne 236f
	jmp 237f
236:
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 34816
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 95232
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 22528
	mov ecx, 128
238:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 238b
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 22528
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 22528
	mov edx, 95232
	mov rcx, rbx
	add rcx, 10240
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 35840
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 95232
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 23552
	mov ecx, 128
239:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 239b
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 23552
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 23552
	mov edx, 95232
	mov rcx, rbx
	add rcx, 11264
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 36864
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 95232
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 24576
	mov ecx, 128
240:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 240b
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 24576
	mov edx, 95232
	mov rcx, rbx
	add rcx, 12288
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 37888
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 95232
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 25600
	mov ecx, 128
241:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 241b
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 25600
	mov edx, 95232
	mov rcx, rbx
	add rcx, 13312
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov eax, DWORD PTR [rbx+904]
	sub rax, 81
	shr rax, 63
	and r15d, eax
237:
227:
	test r15d, r15d
	jne 242f
	mov rax, QWORD PTR [rbx+896]
	add rax, 4
	mov QWORD PTR [rbx+896], rax
	jmp 243f
242:
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
243:
217:
	mov rax, QWORD PTR [rbx+888]
	sub rax, 1
	mov QWORD PTR [rbx+888], rax
	jne 27b
	test r15d, r15d
	jne 244f
	jmp 245f
244:
	mov rdi, r14
	add rdi, 0
	mov rsi, rbx
	add rsi, 1040
	mov ecx, 4
246:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 246b
	mov rdi, rbx
	add rdi, 14336
	mov esi, 131071
	mov edx, 131072
	mov rcx, r14
	add rcx, 32
	mov r8d, 576
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 15360
	mov esi, 131071
	mov edx, 131072
	mov rcx, r14
	add rcx, 608
	mov r8d, 576
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 131071
	mov edx, 131072
	mov rcx, r14
	add rcx, 1184
	mov r8d, 576
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 131071
	mov edx, 131072
	mov rcx, r14
	add rcx, 1760
	mov r8d, 576
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 10240
	mov esi, 1024
	mov edx, 80
	mov rcx, r14
	add rcx, 2336
	mov r8d, 84
	call {vg_mldsa_hint_bit_pack}
245:
26:
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6

vg_mldsa44_sign_message:
	cmp r8, 256
	jb 20f
	mov eax, 2
	jmp 21f
20:
	mov r10, QWORD PTR [rsp+8]
	mov r11, QWORD PTR [rsp+16]
	mov eax, 0
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r10
	push r9
	push r11
	push rax
	mov BYTE PTR [rsp+1], r8b
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 78024
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 78664
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 78664
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	call {vg_mldsa44_sign}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
21:
	ret
	.p2align 6

vg_mldsa44_verify:
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
	mov rdi, r13
	add rdi, 2336
	mov esi, 84
	mov edx, 80
	mov rcx, rbx
	add rcx, 8192
	mov r8d, 1024
	call {vg_mldsa_hint_bit_unpack}
	mov r15d, eax
	test r15d, r15d
	jne 20f
	jmp 21f
20:
	mov rdi, r13
	add rdi, 32
	mov esi, 576
	mov edx, 131071
	mov ecx, 131072
	mov r8, rbx
	add r8, 16384
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 130994
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 608
	mov esi, 576
	mov edx, 131071
	mov ecx, 131072
	mov r8, rbx
	add r8, 17408
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 130994
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 1184
	mov esi, 576
	mov edx, 131071
	mov ecx, 131072
	mov r8, rbx
	add r8, 18432
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 130994
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 1760
	mov esi, 576
	mov edx, 131071
	mov ecx, 131072
	mov r8, rbx
	add r8, 19456
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 130994
	call {vg_mldsa_norm_lt}
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
	add rdx, 61440
	call {vg_mldsa_rej_ntt_poly4}
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
	mov eax, 0
	mov BYTE PTR [rbx+2592], al
	mov eax, 1
	mov BYTE PTR [rbx+2593], al
	mov eax, 1
	mov BYTE PTR [rbx+2626], al
	mov eax, 1
	mov BYTE PTR [rbx+2627], al
	mov eax, 2
	mov BYTE PTR [rbx+2660], al
	mov eax, 1
	mov BYTE PTR [rbx+2661], al
	mov eax, 3
	mov BYTE PTR [rbx+2694], al
	mov eax, 1
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_rej_ntt_poly4}
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
	mov eax, 0
	mov BYTE PTR [rbx+2592], al
	mov eax, 2
	mov BYTE PTR [rbx+2593], al
	mov eax, 1
	mov BYTE PTR [rbx+2626], al
	mov eax, 2
	mov BYTE PTR [rbx+2627], al
	mov eax, 2
	mov BYTE PTR [rbx+2660], al
	mov eax, 2
	mov BYTE PTR [rbx+2661], al
	mov eax, 3
	mov BYTE PTR [rbx+2694], al
	mov eax, 2
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_rej_ntt_poly4}
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
	mov eax, 0
	mov BYTE PTR [rbx+2592], al
	mov eax, 3
	mov BYTE PTR [rbx+2593], al
	mov eax, 1
	mov BYTE PTR [rbx+2626], al
	mov eax, 3
	mov BYTE PTR [rbx+2627], al
	mov eax, 2
	mov BYTE PTR [rbx+2660], al
	mov eax, 3
	mov BYTE PTR [rbx+2661], al
	mov eax, 3
	mov BYTE PTR [rbx+2694], al
	mov eax, 3
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_rej_ntt_poly4}
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
	mov rdi, r13
	add rdi, 0
	mov esi, 32
	mov edx, 39
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
213:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 213b
	mov rdi, rbx
	add rdi, 16384
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 17408
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 30720
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 31744
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbp
	add rdi, 32
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 26624
	mov edx, 95232
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 43
	mov rdx, rbx
	add rdx, 1024
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 34816
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 35840
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 26624
	mov edx, 95232
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 43
	mov rdx, rbx
	add rdx, 1216
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 37888
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 39936
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 10240
	mov rsi, rbx
	add rsi, 26624
	mov edx, 95232
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 43
	mov rdx, rbx
	add rdx, 1408
	mov ecx, 192
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 41984
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 44032
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 24576
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 24576
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 25600
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 11264
	mov rsi, rbx
	add rsi, 26624
	mov edx, 95232
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 43
	mov rdx, rbx
	add rdx, 1600
	mov ecx, 192
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
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 2048
	mov rdi, r13
	add rdi, 0
	mov ecx, 32
	mov edx, 0
214:
	movzx eax, BYTE PTR [rsi]
	movzx r8d, BYTE PTR [rdi]
	xor rax, r8
	or rdx, rax
	add rsi, 1
	add rdi, 1
	sub rcx, 1
	jne 214b
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

vg_mldsa44_verify_message_cached:
	cmp r8, 256
	jb 20f
	mov eax, 2
	jmp 21f
20:
	mov r11, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [rsp+16]
	mov eax, 0
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push r10
	push r11
	push rax
	mov BYTE PTR [rsp+1], r8b
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 78024
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 77824
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 78664
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 78024
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 78664
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	call {vg_mldsa44_verify}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
21:
	ret
	.p2align 6
