// The functions of `src/mldsa44.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_keygen_avx512:
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
	call {vg_mldsa_rej_ntt_poly4_avx512}
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
	call {vg_mldsa_rej_ntt_poly4_avx512}
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
	call {vg_mldsa_rej_ntt_poly4_avx512}
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
	call {vg_mldsa_rej_ntt_poly4_avx512}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4_avx2}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4_avx2}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4_avx2}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4_avx2}
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
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-32]
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+32]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4_avx2}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4_avx2}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4_avx2}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4_avx2}
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
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-32]
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+32]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4}
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
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse4}
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
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_pk_tr:
	mov QWORD PTR [rdx+840], rbx
	mov QWORD PTR [rdx+848], rbp
	mov QWORD PTR [rdx+856], r12
	mov QWORD PTR [rdx+864], r13
	mov QWORD PTR [rdx+872], r14
	mov QWORD PTR [rdx+880], r15
	mov rbx, rdx
	mov r12, rdi
	mov r13, rsi
	mov r15d, 1
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
	add rcx, 0
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
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_prepare_verifying_key_avx2:
	mov QWORD PTR [rdx+840], rbx
	mov QWORD PTR [rdx+848], rbp
	mov QWORD PTR [rdx+856], r12
	mov QWORD PTR [rdx+864], r13
	mov QWORD PTR [rdx+872], r14
	mov QWORD PTR [rdx+880], r15
	mov rbx, rsi
	mov rbp, rdi
	mov r12, rdx
	mov r13, rdx
	mov rdi, rbp
	add rdi, 32
	mov rsi, rbx
	add rsi, 1312
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 1312
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 2336
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2336
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 3360
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 3360
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 4384
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4384
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 164
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rbx, QWORD PTR [r12+840]
	mov rbp, QWORD PTR [r12+848]
	mov r13, QWORD PTR [r12+864]
	mov r14, QWORD PTR [r12+872]
	mov r15, QWORD PTR [r12+880]
	mov r12, QWORD PTR [r12+856]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	lea rsp, [rsp-32]
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_prepare_signing_key_avx2:
	mov QWORD PTR [rdx+840], rbx
	mov QWORD PTR [rdx+848], rbp
	mov QWORD PTR [rdx+856], r12
	mov QWORD PTR [rdx+864], r13
	mov QWORD PTR [rdx+872], r14
	mov QWORD PTR [rdx+880], r15
	mov rbx, rsi
	mov rbp, rdi
	mov r12, rdx
	mov r13, rdx
	mov rdi, rbp
	add rdi, 128
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 2560
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 3584
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 3584
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 4608
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4608
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 5632
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5632
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 6656
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6656
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 7680
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7680
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 8704
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8704
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 9728
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 9728
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 896
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 10752
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10752
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1312
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 11776
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11776
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1728
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 12800
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12800
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2144
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 13824
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13824
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 320
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rbx, QWORD PTR [r12+840]
	mov rbp, QWORD PTR [r12+848]
	mov r13, QWORD PTR [r12+864]
	mov r14, QWORD PTR [r12+872]
	mov r15, QWORD PTR [r12+880]
	mov r12, QWORD PTR [r12+856]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	lea rsp, [rsp-32]
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_prepare_verifying_key:
	mov QWORD PTR [rdx+840], rbx
	mov QWORD PTR [rdx+848], rbp
	mov QWORD PTR [rdx+856], r12
	mov QWORD PTR [rdx+864], r13
	mov QWORD PTR [rdx+872], r14
	mov QWORD PTR [rdx+880], r15
	mov rbx, rsi
	mov rbp, rdi
	mov r12, rdx
	mov r13, rdx
	mov rdi, rbp
	add rdi, 32
	mov rsi, rbx
	add rsi, 1312
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 1312
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 2336
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2336
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 3360
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 3360
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 4384
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4384
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 164
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rbx, QWORD PTR [r12+840]
	mov rbp, QWORD PTR [r12+848]
	mov r13, QWORD PTR [r12+864]
	mov r14, QWORD PTR [r12+872]
	mov r15, QWORD PTR [r12+880]
	mov r12, QWORD PTR [r12+856]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	lea rsp, [rsp-32]
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_prepare_signing_key:
	mov QWORD PTR [rdx+840], rbx
	mov QWORD PTR [rdx+848], rbp
	mov QWORD PTR [rdx+856], r12
	mov QWORD PTR [rdx+864], r13
	mov QWORD PTR [rdx+872], r14
	mov QWORD PTR [rdx+880], r15
	mov rbx, rsi
	mov rbp, rdi
	mov r12, rdx
	mov r13, rdx
	mov rdi, rbp
	add rdi, 128
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 2560
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 3584
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 3584
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 4608
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4608
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 5632
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5632
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 6656
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6656
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 7680
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7680
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 8704
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8704
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 9728
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 9728
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 896
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 10752
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10752
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1312
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 11776
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11776
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1728
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 12800
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12800
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2144
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 13824
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13824
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 320
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rbx, QWORD PTR [r12+840]
	mov rbp, QWORD PTR [r12+848]
	mov r13, QWORD PTR [r12+864]
	mov r14, QWORD PTR [r12+872]
	mov r15, QWORD PTR [r12+880]
	mov r12, QWORD PTR [r12+856]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	lea rsp, [rsp-32]
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_avx512:
	mov r9d, 0
	call {vg_mldsa44_sign_with_cache_avx512}
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_prepared_avx512:
	mov r9d, 1
	call {vg_mldsa44_sign_with_cache_avx512}
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_avx2:
	mov r9d, 0
	call {vg_mldsa44_sign_with_cache_avx2}
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_prepared_avx2:
	mov r9d, 1
	call {vg_mldsa44_sign_with_cache_avx2}
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign:
	mov r9d, 0
	call {vg_mldsa44_sign_with_cache}
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-40]
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_prepared:
	mov r9d, 1
	call {vg_mldsa44_sign_with_cache}
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-40]
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_message_avx512:
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
	mov r9d, 0
	call {vg_mldsa44_sign_with_cache_avx512}
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
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-112]
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_message_prepared_avx512:
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
	mov r9d, 1
	call {vg_mldsa44_sign_with_cache_avx512}
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
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-112]
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
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
	mov r9d, 0
	call {vg_mldsa44_sign_with_cache_avx2}
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
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-112]
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_message_prepared_avx2:
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
	mov r9d, 1
	call {vg_mldsa44_sign_with_cache_avx2}
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
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-112]
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
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
	mov r9d, 0
	call {vg_mldsa44_sign_with_cache}
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
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-112]
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_sign_message_prepared:
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
	mov r9d, 1
	call {vg_mldsa44_sign_with_cache}
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
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-112]
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_avx512:
	mov r8d, 0
	call {vg_mldsa44_verify_with_cache_avx512}
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_prepared_avx512:
	mov r8d, 1
	call {vg_mldsa44_verify_with_cache_avx512}
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_avx2:
	mov r8d, 0
	call {vg_mldsa44_verify_with_cache_avx2}
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_prepared_avx2:
	mov r8d, 1
	call {vg_mldsa44_verify_with_cache_avx2}
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify:
	mov r8d, 0
	call {vg_mldsa44_verify_with_cache}
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-40]
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_prepared:
	mov r8d, 1
	call {vg_mldsa44_verify_with_cache}
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-40]
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+40]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_message_cached_avx512:
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
	mov r8d, 0
	call {vg_mldsa44_verify_with_cache_avx512}
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
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-112]
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_message_prepared_avx512:
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
	mov r8d, 1
	call {vg_mldsa44_verify_with_cache_avx512}
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
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-112]
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
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
	mov r8d, 0
	call {vg_mldsa44_verify_with_cache_avx2}
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
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-112]
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_message_prepared_avx2:
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
	mov r8d, 1
	call {vg_mldsa44_verify_with_cache_avx2}
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
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-112]
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
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
	mov r8d, 0
	call {vg_mldsa44_verify_with_cache}
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
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-112]
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_mldsa44_verify_message_prepared:
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
	mov r8d, 1
	call {vg_mldsa44_verify_with_cache}
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
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-112]
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6
