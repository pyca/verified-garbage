// The functions of `src/internal/vg_mldsa65_sign_with_cache_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_sign_with_cache_avx512:
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
	mov QWORD PTR [r8+952], r9
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
	add rsi, 50176
	mov rdx, rbx
	add rdx, 80896
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov eax, 4
	mov BYTE PTR [rbx+1184], al
	mov eax, 0
	mov BYTE PTR [rbx+1185], al
	mov eax, 0
	mov BYTE PTR [rbx+1218], al
	mov eax, 1
	mov BYTE PTR [rbx+1219], al
	mov eax, 1
	mov BYTE PTR [rbx+1252], al
	mov eax, 1
	mov BYTE PTR [rbx+1253], al
	mov eax, 2
	mov BYTE PTR [rbx+1286], al
	mov eax, 1
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 54272
	mov rdx, rbx
	add rdx, 80896
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov eax, 3
	mov BYTE PTR [rbx+1184], al
	mov eax, 1
	mov BYTE PTR [rbx+1185], al
	mov eax, 4
	mov BYTE PTR [rbx+1218], al
	mov eax, 1
	mov BYTE PTR [rbx+1219], al
	mov eax, 0
	mov BYTE PTR [rbx+1252], al
	mov eax, 2
	mov BYTE PTR [rbx+1253], al
	mov eax, 1
	mov BYTE PTR [rbx+1286], al
	mov eax, 2
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 58368
	mov rdx, rbx
	add rdx, 80896
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov eax, 2
	mov BYTE PTR [rbx+1184], al
	mov eax, 2
	mov BYTE PTR [rbx+1185], al
	mov eax, 3
	mov BYTE PTR [rbx+1218], al
	mov eax, 2
	mov BYTE PTR [rbx+1219], al
	mov eax, 4
	mov BYTE PTR [rbx+1252], al
	mov eax, 2
	mov BYTE PTR [rbx+1253], al
	mov eax, 0
	mov BYTE PTR [rbx+1286], al
	mov eax, 3
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 62464
	mov rdx, rbx
	add rdx, 80896
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov eax, 1
	mov BYTE PTR [rbx+1184], al
	mov eax, 3
	mov BYTE PTR [rbx+1185], al
	mov eax, 2
	mov BYTE PTR [rbx+1218], al
	mov eax, 3
	mov BYTE PTR [rbx+1219], al
	mov eax, 3
	mov BYTE PTR [rbx+1252], al
	mov eax, 3
	mov BYTE PTR [rbx+1253], al
	mov eax, 4
	mov BYTE PTR [rbx+1286], al
	mov eax, 3
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 66560
	mov rdx, rbx
	add rdx, 80896
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov eax, 0
	mov BYTE PTR [rbx+1184], al
	mov eax, 4
	mov BYTE PTR [rbx+1185], al
	mov eax, 1
	mov BYTE PTR [rbx+1218], al
	mov eax, 4
	mov BYTE PTR [rbx+1219], al
	mov eax, 2
	mov BYTE PTR [rbx+1252], al
	mov eax, 4
	mov BYTE PTR [rbx+1253], al
	mov eax, 3
	mov BYTE PTR [rbx+1286], al
	mov eax, 4
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 70656
	mov rdx, rbx
	add rdx, 80896
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov eax, 4
	mov BYTE PTR [rbx+1184], al
	mov eax, 4
	mov BYTE PTR [rbx+1185], al
	mov eax, 0
	mov BYTE PTR [rbx+1218], al
	mov eax, 5
	mov BYTE PTR [rbx+1219], al
	mov eax, 1
	mov BYTE PTR [rbx+1252], al
	mov eax, 5
	mov BYTE PTR [rbx+1253], al
	mov eax, 2
	mov BYTE PTR [rbx+1286], al
	mov eax, 5
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 74752
	mov rdx, rbx
	add rdx, 80896
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov eax, 3
	mov BYTE PTR [rbx+944], al
	mov eax, 5
	mov BYTE PTR [rbx+945], al
	mov rdi, rbx
	add rdi, 912
	mov rsi, rbx
	add rsi, 78848
	mov rdx, rbx
	add rdx, 3072
	call {vg_mldsa_rej_ntt_poly}
	and r15d, eax
	mov eax, 4
	mov BYTE PTR [rbx+944], al
	mov eax, 5
	mov BYTE PTR [rbx+945], al
	mov rdi, rbx
	add rdi, 912
	mov rsi, rbx
	add rsi, 79872
	mov rdx, rbx
	add rdx, 3072
	call {vg_mldsa_rej_ntt_poly}
	and r15d, eax
	test r15d, r15d
	jne 25f
	jmp 26f
25:
	mov rax, QWORD PTR [rbx+952]
	test rax, rax
	jne 27f
	mov rdi, rbp
	add rdi, 128
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 32768
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 256
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 33792
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 384
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 34816
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 512
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 35840
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 640
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 36864
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 768
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 37888
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 896
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 38912
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1024
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 39936
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 39936
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1152
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 40960
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 40960
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 41984
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 41984
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1408
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 43008
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 43008
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1536
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 44032
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 44032
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1952
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 45056
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 45056
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 2368
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 46080
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 2784
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 47104
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 47104
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 3200
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 48128
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 48128
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 3616
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 49152
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 49152
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
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
	jmp 28f
27:
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbp
	add rsi, 4032
	mov ecx, 2176
29:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 29b
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
28:
	mov eax, 0
	mov QWORD PTR [rbx+896], rax
	mov eax, 814
	mov QWORD PTR [rbx+888], rax
210:
	mov rdi, rbx
	add rdi, 1296
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
	add rax, 0
	mov BYTE PTR [rbx+1360], al
	shr rax, 8
	mov BYTE PTR [rbx+1361], al
	mov rdi, rbx
	add rdi, 1362
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
212:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 212b
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
213:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 213b
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
214:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 214b
	mov rax, QWORD PTR [rbx+896]
	add rax, 3
	mov BYTE PTR [rbx+1558], al
	shr rax, 8
	mov BYTE PTR [rbx+1559], al
	mov rdi, rbx
	add rdi, 1296
	mov esi, 524288
	mov rdx, rbx
	add rdx, 16384
	mov rcx, rbx
	add rcx, 80896
	call {vg_mldsa_expand_mask_poly4_avx512}
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 16384
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
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 17408
	mov ecx, 128
216:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 216b
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 18432
	mov ecx, 128
217:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 217b
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 19456
	mov ecx, 128
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 218b
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rax, QWORD PTR [rbx+896]
	add rax, 4
	mov BYTE PTR [rbx+1024], al
	shr rax, 8
	mov BYTE PTR [rbx+1025], al
	mov rdi, rbx
	add rdi, 960
	mov esi, 524288
	mov rdx, rbx
	add rdx, 20480
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_expand_mask_poly}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 20480
	mov ecx, 128
219:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 219b
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 50176
	mov rdx, rbx
	add rdx, 21504
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 55296
	mov rdx, rbx
	add rdx, 21504
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 60416
	mov rdx, rbx
	add rdx, 21504
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 65536
	mov rdx, rbx
	add rdx, 21504
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 70656
	mov rdx, rbx
	add rdx, 21504
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 75776
	mov rdx, rbx
	add rdx, 21504
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 26624
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2048
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2176
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 28672
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2304
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2432
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2560
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 31744
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2688
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
	mov r8d, 48
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, rbx
	add rdi, 1040
	mov esi, 48
	mov edx, 49
	mov rcx, rbx
	add rcx, 5120
	mov r8, rbx
	add r8, 3072
	call {vg_mldsa_sample_in_ball}
	test eax, eax
	jne 220f
	mov r15d, 0
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
	jmp 221f
220:
	mov rdi, rbx
	add rdi, 5120
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx512}
	mov r15d, 1
	mov eax, 0
	mov QWORD PTR [rbx+904], rax
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 32768
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 16384
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx512}
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
	add rdx, 33792
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 17408
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 224f
	jmp 225f
224:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 34816
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 226f
	jmp 227f
226:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 35840
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx512}
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
	add rdx, 36864
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 20480
	mov esi, 524092
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 230f
	jmp 231f
230:
231:
229:
227:
225:
223:
	test r15d, r15d
	jne 232f
	jmp 233f
232:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 37888
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 26624
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx512}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261692
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 234f
	jmp 235f
234:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 38912
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx512}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261692
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 236f
	jmp 237f
236:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 39936
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 28672
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx512}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261692
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 238f
	jmp 239f
238:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 40960
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 29696
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx512}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261692
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 240f
	jmp 241f
240:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 41984
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 30720
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx512}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261692
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 242f
	jmp 243f
242:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 43008
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 31744
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx512}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261692
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	test r15d, r15d
	jne 244f
	jmp 245f
244:
245:
243:
241:
239:
237:
235:
	test r15d, r15d
	jne 246f
	jmp 247f
246:
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 44032
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 26624
	mov ecx, 128
248:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 248b
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 26624
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 10240
	call {vg_mldsa_make_hint_avx512}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 45056
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 27648
	mov ecx, 128
249:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 249b
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 27648
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 27648
	mov edx, 261888
	mov rcx, rbx
	add rcx, 11264
	call {vg_mldsa_make_hint_avx512}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 46080
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 28672
	mov ecx, 128
250:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 250b
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 28672
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 28672
	mov edx, 261888
	mov rcx, rbx
	add rcx, 12288
	call {vg_mldsa_make_hint_avx512}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 47104
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 29696
	mov ecx, 128
251:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 251b
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 29696
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 29696
	mov edx, 261888
	mov rcx, rbx
	add rcx, 13312
	call {vg_mldsa_make_hint_avx512}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 30720
	mov ecx, 128
252:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 252b
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 30720
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 30720
	mov edx, 261888
	mov rcx, rbx
	add rcx, 14336
	call {vg_mldsa_make_hint_avx512}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 49152
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 31744
	mov ecx, 128
253:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 253b
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 31744
	call {vg_mldsa_sub_avx512}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 31744
	mov edx, 261888
	mov rcx, rbx
	add rcx, 15360
	call {vg_mldsa_make_hint_avx512}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov eax, DWORD PTR [rbx+904]
	sub rax, 56
	shr rax, 63
	and r15d, eax
247:
233:
	test r15d, r15d
	jne 254f
	mov rax, QWORD PTR [rbx+896]
	add rax, 5
	mov QWORD PTR [rbx+896], rax
	jmp 255f
254:
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
255:
221:
	mov rax, QWORD PTR [rbx+888]
	sub rax, 1
	mov QWORD PTR [rbx+888], rax
	jne 210b
	test r15d, r15d
	jne 256f
	jmp 257f
256:
	mov rdi, r14
	add rdi, 0
	mov rsi, rbx
	add rsi, 1040
	mov ecx, 6
258:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 258b
	mov rdi, rbx
	add rdi, 16384
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 48
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 688
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 1328
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 1968
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 20480
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 2608
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 10240
	mov esi, 1536
	mov edx, 55
	mov rcx, r14
	add rcx, 3248
	mov r8d, 61
	call {vg_mldsa_hint_bit_pack}
257:
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
