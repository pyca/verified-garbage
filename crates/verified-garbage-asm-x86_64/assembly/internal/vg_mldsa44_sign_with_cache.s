// The functions of `src/internal/vg_mldsa44_sign_with_cache.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_sign_with_cache:
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
	mov rax, QWORD PTR [rbx+952]
	test rax, rax
	jne 27f
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
	jmp 28f
27:
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbp
	add rsi, 2560
	mov ecx, 1536
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
215:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 215b
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
216:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 216b
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
217:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 217b
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
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 218b
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
	jne 219f
	mov r15d, 0
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
	jmp 220f
219:
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
	jne 221f
	jmp 222f
221:
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
	jne 223f
	jmp 224f
223:
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
	jne 225f
	jmp 226f
225:
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
	jne 227f
	jmp 228f
227:
228:
226:
224:
222:
	test r15d, r15d
	jne 229f
	jmp 230f
229:
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
	jne 231f
	jmp 232f
231:
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
	jne 233f
	jmp 234f
233:
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
	jne 235f
	jmp 236f
235:
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
	jne 237f
	jmp 238f
237:
238:
236:
234:
232:
	test r15d, r15d
	jne 239f
	jmp 240f
239:
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
241:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 241b
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
242:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 242b
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
243:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 243b
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
244:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 244b
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
240:
230:
	test r15d, r15d
	jne 245f
	mov rax, QWORD PTR [rbx+896]
	add rax, 4
	mov QWORD PTR [rbx+896], rax
	jmp 246f
245:
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
246:
220:
	mov rax, QWORD PTR [rbx+888]
	sub rax, 1
	mov QWORD PTR [rbx+888], rax
	jne 210b
	test r15d, r15d
	jne 247f
	jmp 248f
247:
	mov rdi, r14
	add rdi, 0
	mov rsi, rbx
	add rsi, 1040
	mov ecx, 4
249:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 249b
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
248:
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
