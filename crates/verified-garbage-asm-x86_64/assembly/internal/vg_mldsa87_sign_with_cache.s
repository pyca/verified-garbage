// The functions of `src/internal/vg_mldsa87_sign_with_cache.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_sign_with_cache:
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
	add rsi, 64512
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 4
	mov BYTE PTR [rbx+1184], al
	mov eax, 0
	mov BYTE PTR [rbx+1185], al
	mov eax, 5
	mov BYTE PTR [rbx+1218], al
	mov eax, 0
	mov BYTE PTR [rbx+1219], al
	mov eax, 6
	mov BYTE PTR [rbx+1252], al
	mov eax, 0
	mov BYTE PTR [rbx+1253], al
	mov eax, 0
	mov BYTE PTR [rbx+1286], al
	mov eax, 1
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 68608
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 1
	mov BYTE PTR [rbx+1184], al
	mov eax, 1
	mov BYTE PTR [rbx+1185], al
	mov eax, 2
	mov BYTE PTR [rbx+1218], al
	mov eax, 1
	mov BYTE PTR [rbx+1219], al
	mov eax, 3
	mov BYTE PTR [rbx+1252], al
	mov eax, 1
	mov BYTE PTR [rbx+1253], al
	mov eax, 4
	mov BYTE PTR [rbx+1286], al
	mov eax, 1
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 72704
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 5
	mov BYTE PTR [rbx+1184], al
	mov eax, 1
	mov BYTE PTR [rbx+1185], al
	mov eax, 6
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
	add rsi, 76800
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
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
	mov eax, 5
	mov BYTE PTR [rbx+1286], al
	mov eax, 2
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 80896
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 6
	mov BYTE PTR [rbx+1184], al
	mov eax, 2
	mov BYTE PTR [rbx+1185], al
	mov eax, 0
	mov BYTE PTR [rbx+1218], al
	mov eax, 3
	mov BYTE PTR [rbx+1219], al
	mov eax, 1
	mov BYTE PTR [rbx+1252], al
	mov eax, 3
	mov BYTE PTR [rbx+1253], al
	mov eax, 2
	mov BYTE PTR [rbx+1286], al
	mov eax, 3
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 84992
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 3
	mov BYTE PTR [rbx+1184], al
	mov eax, 3
	mov BYTE PTR [rbx+1185], al
	mov eax, 4
	mov BYTE PTR [rbx+1218], al
	mov eax, 3
	mov BYTE PTR [rbx+1219], al
	mov eax, 5
	mov BYTE PTR [rbx+1252], al
	mov eax, 3
	mov BYTE PTR [rbx+1253], al
	mov eax, 6
	mov BYTE PTR [rbx+1286], al
	mov eax, 3
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 89088
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
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
	add rsi, 93184
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 4
	mov BYTE PTR [rbx+1184], al
	mov eax, 4
	mov BYTE PTR [rbx+1185], al
	mov eax, 5
	mov BYTE PTR [rbx+1218], al
	mov eax, 4
	mov BYTE PTR [rbx+1219], al
	mov eax, 6
	mov BYTE PTR [rbx+1252], al
	mov eax, 4
	mov BYTE PTR [rbx+1253], al
	mov eax, 0
	mov BYTE PTR [rbx+1286], al
	mov eax, 5
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 97280
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 1
	mov BYTE PTR [rbx+1184], al
	mov eax, 5
	mov BYTE PTR [rbx+1185], al
	mov eax, 2
	mov BYTE PTR [rbx+1218], al
	mov eax, 5
	mov BYTE PTR [rbx+1219], al
	mov eax, 3
	mov BYTE PTR [rbx+1252], al
	mov eax, 5
	mov BYTE PTR [rbx+1253], al
	mov eax, 4
	mov BYTE PTR [rbx+1286], al
	mov eax, 5
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 101376
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 5
	mov BYTE PTR [rbx+1184], al
	mov eax, 5
	mov BYTE PTR [rbx+1185], al
	mov eax, 6
	mov BYTE PTR [rbx+1218], al
	mov eax, 5
	mov BYTE PTR [rbx+1219], al
	mov eax, 0
	mov BYTE PTR [rbx+1252], al
	mov eax, 6
	mov BYTE PTR [rbx+1253], al
	mov eax, 1
	mov BYTE PTR [rbx+1286], al
	mov eax, 6
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 105472
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 2
	mov BYTE PTR [rbx+1184], al
	mov eax, 6
	mov BYTE PTR [rbx+1185], al
	mov eax, 3
	mov BYTE PTR [rbx+1218], al
	mov eax, 6
	mov BYTE PTR [rbx+1219], al
	mov eax, 4
	mov BYTE PTR [rbx+1252], al
	mov eax, 6
	mov BYTE PTR [rbx+1253], al
	mov eax, 5
	mov BYTE PTR [rbx+1286], al
	mov eax, 6
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 109568
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 6
	mov BYTE PTR [rbx+1184], al
	mov eax, 6
	mov BYTE PTR [rbx+1185], al
	mov eax, 0
	mov BYTE PTR [rbx+1218], al
	mov eax, 7
	mov BYTE PTR [rbx+1219], al
	mov eax, 1
	mov BYTE PTR [rbx+1252], al
	mov eax, 7
	mov BYTE PTR [rbx+1253], al
	mov eax, 2
	mov BYTE PTR [rbx+1286], al
	mov eax, 7
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 113664
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov eax, 3
	mov BYTE PTR [rbx+1184], al
	mov eax, 7
	mov BYTE PTR [rbx+1185], al
	mov eax, 4
	mov BYTE PTR [rbx+1218], al
	mov eax, 7
	mov BYTE PTR [rbx+1219], al
	mov eax, 5
	mov BYTE PTR [rbx+1252], al
	mov eax, 7
	mov BYTE PTR [rbx+1253], al
	mov eax, 6
	mov BYTE PTR [rbx+1286], al
	mov eax, 7
	mov BYTE PTR [rbx+1287], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 117760
	mov rdx, rbx
	add rdx, 121856
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
	add r8, 40960
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 40960
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 41984
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 41984
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 43008
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 43008
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 44032
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 44032
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 45056
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 45056
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 46080
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 47104
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 47104
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 48128
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 48128
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 896
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 49152
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 49152
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 992
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 50176
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 50176
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1088
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 51200
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 51200
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1184
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 52224
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 52224
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 53248
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 53248
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1376
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 54272
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 54272
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1472
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 55296
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 55296
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1568
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 56320
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 56320
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1984
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 57344
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 57344
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2400
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 58368
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 58368
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2816
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 59392
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 59392
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 3232
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 60416
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 60416
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 3648
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 61440
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 61440
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 4064
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 62464
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 62464
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 4480
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 63488
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 63488
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
	add rdi, 40960
	mov rsi, rbp
	add rsi, 4896
	mov ecx, 2944
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
	add rdx, 18432
	mov rcx, rbx
	add rcx, 121856
	call {vg_mldsa_expand_mask_poly4}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 18432
	mov ecx, 128
215:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 215b
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 19456
	mov ecx, 128
216:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 216b
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 20480
	mov ecx, 128
217:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 217b
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 21504
	mov ecx, 128
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 218b
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 1296
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
219:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 219b
	mov rax, QWORD PTR [rbx+896]
	add rax, 4
	mov BYTE PTR [rbx+1360], al
	shr rax, 8
	mov BYTE PTR [rbx+1361], al
	mov rdi, rbx
	add rdi, 1362
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
220:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 220b
	mov rax, QWORD PTR [rbx+896]
	add rax, 5
	mov BYTE PTR [rbx+1426], al
	shr rax, 8
	mov BYTE PTR [rbx+1427], al
	mov rdi, rbx
	add rdi, 1428
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
221:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 221b
	mov rax, QWORD PTR [rbx+896]
	add rax, 6
	mov BYTE PTR [rbx+1492], al
	shr rax, 8
	mov BYTE PTR [rbx+1493], al
	mov rdi, rbx
	add rdi, 1494
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
222:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 222b
	mov rax, QWORD PTR [rbx+896]
	add rax, 7
	mov BYTE PTR [rbx+1558], al
	shr rax, 8
	mov BYTE PTR [rbx+1559], al
	mov rdi, rbx
	add rdi, 1296
	mov esi, 524288
	mov rdx, rbx
	add rdx, 6144
	mov rcx, rbx
	add rcx, 121856
	call {vg_mldsa_expand_mask_poly4}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 6144
	mov ecx, 128
223:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 223b
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 22528
	mov ecx, 128
224:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 224b
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 7168
	mov ecx, 128
225:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 225b
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 23552
	mov ecx, 128
226:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 226b
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 8192
	mov ecx, 128
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 227b
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 24576
	mov ecx, 128
228:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 228b
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 64512
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7}
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 71680
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 78848
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 86016
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 93184
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 100352
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7}
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 107520
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7}
	mov rdi, rbx
	add rdi, 39936
	mov rsi, rbx
	add rsi, 114688
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7}
	mov rdi, rbx
	add rdi, 32768
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2048
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 33792
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2176
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 34816
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2304
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 35840
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2432
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 36864
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2560
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 37888
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2688
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 38912
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2816
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 39936
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits}
	mov rdi, rbx
	add rdi, 6144
	mov esi, 15
	mov rdx, rbx
	add rdx, 2944
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
	mov r8d, 1024
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
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
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, rbx
	add rdi, 1040
	mov esi, 64
	mov edx, 60
	mov rcx, rbx
	add rcx, 5120
	mov r8, rbx
	add r8, 3072
	call {vg_mldsa_sample_in_ball}
	test eax, eax
	jne 229f
	mov r15d, 0
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
	jmp 230f
229:
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
	add rdx, 40960
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 524168
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
	add rdx, 41984
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 524168
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
	add rdx, 43008
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 20480
	mov esi, 524168
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
	add rdx, 44032
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 21504
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 237f
	jmp 238f
237:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 45056
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
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 239f
	jmp 240f
239:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 46080
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
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 241f
	jmp 242f
241:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 47104
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
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 243f
	jmp 244f
243:
244:
242:
240:
238:
236:
234:
232:
	test r15d, r15d
	jne 245f
	jmp 246f
245:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 32768
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 247f
	jmp 248f
247:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 49152
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 33792
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 249f
	jmp 250f
249:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 50176
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 34816
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 251f
	jmp 252f
251:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 51200
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 35840
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 253f
	jmp 254f
253:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 52224
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 36864
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 255f
	jmp 256f
255:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 53248
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 37888
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 257f
	jmp 258f
257:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 54272
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 38912
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 259f
	jmp 260f
259:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 39936
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 39936
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt}
	and r15d, eax
	test r15d, r15d
	jne 261f
	jmp 262f
261:
262:
260:
258:
256:
254:
252:
250:
248:
	test r15d, r15d
	jne 263f
	jmp 264f
263:
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 56320
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 32768
	mov ecx, 128
265:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 265b
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 32768
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 32768
	mov edx, 261888
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
	add rdx, 57344
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 33792
	mov ecx, 128
266:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 266b
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 33792
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 33792
	mov edx, 261888
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
	add rdx, 58368
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 34816
	mov ecx, 128
267:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 267b
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 34816
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 34816
	mov edx, 261888
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
	add rdx, 59392
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 35840
	mov ecx, 128
268:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 268b
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 35840
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 35840
	mov edx, 261888
	mov rcx, rbx
	add rcx, 13312
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 60416
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 36864
	mov ecx, 128
269:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 269b
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 36864
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 36864
	mov edx, 261888
	mov rcx, rbx
	add rcx, 14336
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 37888
	mov ecx, 128
270:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 270b
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 37888
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 37888
	mov edx, 261888
	mov rcx, rbx
	add rcx, 15360
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 38912
	mov ecx, 128
271:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 271b
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 38912
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 38912
	mov edx, 261888
	mov rcx, rbx
	add rcx, 16384
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 39936
	mov ecx, 128
272:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 272b
	mov rdi, rbx
	add rdi, 39936
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 39936
	call {vg_mldsa_sub}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 39936
	mov edx, 261888
	mov rcx, rbx
	add rcx, 17408
	call {vg_mldsa_make_hint}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov eax, DWORD PTR [rbx+904]
	sub rax, 76
	shr rax, 63
	and r15d, eax
264:
246:
	test r15d, r15d
	jne 273f
	mov rax, QWORD PTR [rbx+896]
	add rax, 7
	mov QWORD PTR [rbx+896], rax
	jmp 274f
273:
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
274:
230:
	mov rax, QWORD PTR [rbx+888]
	sub rax, 1
	mov QWORD PTR [rbx+888], rax
	jne 210b
	test r15d, r15d
	jne 275f
	jmp 276f
275:
	mov rdi, r14
	add rdi, 0
	mov rsi, rbx
	add rsi, 1040
	mov ecx, 8
277:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 277b
	mov rdi, rbx
	add rdi, 18432
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 64
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 704
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 20480
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 1344
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 21504
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 1984
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 2624
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 3264
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 524287
	mov edx, 524288
	mov rcx, r14
	add rcx, 3904
	mov r8d, 640
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 10240
	mov esi, 2048
	mov edx, 75
	mov rcx, r14
	add rcx, 4544
	mov r8d, 83
	call {vg_mldsa_hint_bit_pack}
276:
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
