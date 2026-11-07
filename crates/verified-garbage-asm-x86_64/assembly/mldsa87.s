// The functions of `src/mldsa87.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_pk_tr:
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
	mov r8d, 2592
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 8
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
	ret
	.p2align 6

vg_mldsa87_keygen_avx2:
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
	mov eax, 8
	mov BYTE PTR [rbx+896], al
	mov eax, 7
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
	add rdx, 79872
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
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 0
	mov BYTE PTR [rbx+1441], al
	mov eax, 5
	mov BYTE PTR [rbx+1474], al
	mov eax, 0
	mov BYTE PTR [rbx+1475], al
	mov eax, 6
	mov BYTE PTR [rbx+1508], al
	mov eax, 0
	mov BYTE PTR [rbx+1509], al
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 1
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 5
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 6
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 0
	mov BYTE PTR [rbx+1508], al
	mov eax, 2
	mov BYTE PTR [rbx+1509], al
	mov eax, 1
	mov BYTE PTR [rbx+1542], al
	mov eax, 2
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 2
	mov BYTE PTR [rbx+1440], al
	mov eax, 2
	mov BYTE PTR [rbx+1441], al
	mov eax, 3
	mov BYTE PTR [rbx+1474], al
	mov eax, 2
	mov BYTE PTR [rbx+1475], al
	mov eax, 4
	mov BYTE PTR [rbx+1508], al
	mov eax, 2
	mov BYTE PTR [rbx+1509], al
	mov eax, 5
	mov BYTE PTR [rbx+1542], al
	mov eax, 2
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 20480
	mov ecx, 1024
210:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 210b
	mov eax, 6
	mov BYTE PTR [rbx+1440], al
	mov eax, 2
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 24576
	mov ecx, 1024
211:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 211b
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 3
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 5
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 6
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 28672
	mov ecx, 1024
212:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 212b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 4
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 4
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 4
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 32768
	mov ecx, 1024
213:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 213b
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 5
	mov BYTE PTR [rbx+1474], al
	mov eax, 4
	mov BYTE PTR [rbx+1475], al
	mov eax, 6
	mov BYTE PTR [rbx+1508], al
	mov eax, 4
	mov BYTE PTR [rbx+1509], al
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 36864
	mov ecx, 1024
214:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 214b
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 5
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 5
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 40960
	mov ecx, 1024
215:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 215b
	mov eax, 5
	mov BYTE PTR [rbx+1440], al
	mov eax, 5
	mov BYTE PTR [rbx+1441], al
	mov eax, 6
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 0
	mov BYTE PTR [rbx+1508], al
	mov eax, 6
	mov BYTE PTR [rbx+1509], al
	mov eax, 1
	mov BYTE PTR [rbx+1542], al
	mov eax, 6
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 45056
	mov ecx, 1024
216:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 216b
	mov eax, 2
	mov BYTE PTR [rbx+1440], al
	mov eax, 6
	mov BYTE PTR [rbx+1441], al
	mov eax, 3
	mov BYTE PTR [rbx+1474], al
	mov eax, 6
	mov BYTE PTR [rbx+1475], al
	mov eax, 4
	mov BYTE PTR [rbx+1508], al
	mov eax, 6
	mov BYTE PTR [rbx+1509], al
	mov eax, 5
	mov BYTE PTR [rbx+1542], al
	mov eax, 6
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 49152
	mov ecx, 1024
217:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 217b
	mov eax, 6
	mov BYTE PTR [rbx+1440], al
	mov eax, 6
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 7
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 7
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 7
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 53248
	mov ecx, 1024
218:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 218b
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 7
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
	mov BYTE PTR [rbx+1474], al
	mov eax, 7
	mov BYTE PTR [rbx+1475], al
	mov eax, 5
	mov BYTE PTR [rbx+1508], al
	mov eax, 7
	mov BYTE PTR [rbx+1509], al
	mov eax, 6
	mov BYTE PTR [rbx+1542], al
	mov eax, 7
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 57344
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 57344
	mov ecx, 1024
219:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 219b
	mov eax, 0
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 61440
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 61440
	mov ecx, 256
220:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 220b
	mov eax, 1
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 62464
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 62464
	mov ecx, 256
221:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 221b
	mov eax, 2
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 63488
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 63488
	mov ecx, 256
222:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 222b
	mov eax, 3
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 64512
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 64512
	mov ecx, 256
223:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 223b
	mov eax, 4
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 65536
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 65536
	mov ecx, 256
224:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 224b
	mov eax, 5
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 66560
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 66560
	mov ecx, 256
225:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 225b
	mov eax, 6
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 67584
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 67584
	mov ecx, 256
226:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 226b
	mov eax, 7
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 68608
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 68608
	mov ecx, 256
227:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 227b
	mov eax, 8
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 69632
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 69632
	mov ecx, 256
228:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 228b
	mov eax, 9
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 70656
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 70656
	mov ecx, 256
229:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 229b
	mov eax, 10
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 71680
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 71680
	mov ecx, 256
230:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 230b
	mov eax, 11
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 72704
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 72704
	mov ecx, 256
231:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 231b
	mov eax, 12
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 73728
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 73728
	mov ecx, 256
232:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 232b
	mov eax, 13
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 74752
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 74752
	mov ecx, 256
233:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 233b
	mov eax, 14
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 75776
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 75776
	mov ecx, 256
234:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 234b
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
235:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 235b
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
236:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 236b
	mov rdi, r13
	add rdi, 32
	mov rsi, rbx
	add rsi, 1120
	mov ecx, 4
237:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 237b
	mov rdi, rbx
	add rdi, 61440
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 128
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 62464
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 224
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 63488
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 320
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 64512
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 416
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 65536
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 512
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 66560
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 608
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 67584
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 704
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 68608
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 800
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 69632
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 896
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 70656
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 992
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 71680
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1088
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 72704
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1184
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 73728
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1280
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 74752
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1376
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 75776
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1472
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 61440
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 62464
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 63488
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 64512
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 65536
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 66560
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 67584
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 6144
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 7168
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 9216
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 10240
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 68608
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 32
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1568
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 11264
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 13312
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 14336
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 15360
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 17408
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 69632
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 352
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1984
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 18432
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 19456
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 21504
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 22528
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 70656
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 672
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2400
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 25600
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 26624
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 27648
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 30720
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 31744
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 71680
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 992
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2816
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 34816
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 35840
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 37888
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 72704
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1312
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3232
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 39936
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 41984
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 44032
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 46080
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 73728
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1632
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3648
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 48128
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 50176
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 52224
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 74752
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1952
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 4064
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 54272
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 55296
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 56320
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 57344
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 58368
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 59392
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 60416
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 75776
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 2272
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 4480
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
	mov r8d, 2592
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 8
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

vg_mldsa87_prepare_verifying_key_avx2:
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
	add rsi, 2592
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2592
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 3616
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 3616
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 4640
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4640
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 5664
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 5664
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1312
	mov rsi, rbx
	add rsi, 6688
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 6688
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1632
	mov rsi, rbx
	add rsi, 7712
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 7712
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1952
	mov rsi, rbx
	add rsi, 8736
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 8736
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2272
	mov rsi, rbx
	add rsi, 9760
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 9760
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 324
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
	ret
	.p2align 6

vg_mldsa87_prepare_signing_key_avx2:
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
	add r8, 4896
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4896
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 5920
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5920
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 6944
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6944
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 7968
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7968
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 8992
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8992
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 10016
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10016
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 11040
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11040
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 12064
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12064
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 896
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 13088
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13088
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 992
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 14112
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 14112
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1088
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 15136
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 15136
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1184
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 16160
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16160
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 17184
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17184
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1376
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 18208
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18208
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1472
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 19232
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19232
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1568
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 20256
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20256
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1984
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 21280
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 21280
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2400
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 22304
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 22304
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2816
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 23328
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 23328
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 3232
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 24352
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 24352
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 3648
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 25376
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 25376
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 4064
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 26400
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 26400
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 4480
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 27424
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 27424
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 612
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
	ret
	.p2align 6

vg_mldsa87_sign_avx2:
	mov r9d, 0
	call {vg_mldsa87_sign_with_cache_avx2}
	ret
	.p2align 6

vg_mldsa87_sign_message_avx2:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 0
	call {vg_mldsa87_sign_with_cache_avx2}
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

vg_mldsa87_sign_message_prepared_avx2:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 1
	call {vg_mldsa87_sign_with_cache_avx2}
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

vg_mldsa87_verify_avx2:
	mov r8d, 0
	call {vg_mldsa87_verify_with_cache_avx2}
	ret
	.p2align 6

vg_mldsa87_verify_message_cached_avx2:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 0
	call {vg_mldsa87_verify_with_cache_avx2}
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

vg_mldsa87_verify_message_prepared_avx2:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 1
	call {vg_mldsa87_verify_with_cache_avx2}
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

vg_mldsa87_keygen_avx512:
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
	mov eax, 8
	mov BYTE PTR [rbx+896], al
	mov eax, 7
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
	add rdx, 79872
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
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 0
	mov BYTE PTR [rbx+1441], al
	mov eax, 5
	mov BYTE PTR [rbx+1474], al
	mov eax, 0
	mov BYTE PTR [rbx+1475], al
	mov eax, 6
	mov BYTE PTR [rbx+1508], al
	mov eax, 0
	mov BYTE PTR [rbx+1509], al
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 1
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 5
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 6
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 0
	mov BYTE PTR [rbx+1508], al
	mov eax, 2
	mov BYTE PTR [rbx+1509], al
	mov eax, 1
	mov BYTE PTR [rbx+1542], al
	mov eax, 2
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 2
	mov BYTE PTR [rbx+1440], al
	mov eax, 2
	mov BYTE PTR [rbx+1441], al
	mov eax, 3
	mov BYTE PTR [rbx+1474], al
	mov eax, 2
	mov BYTE PTR [rbx+1475], al
	mov eax, 4
	mov BYTE PTR [rbx+1508], al
	mov eax, 2
	mov BYTE PTR [rbx+1509], al
	mov eax, 5
	mov BYTE PTR [rbx+1542], al
	mov eax, 2
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 20480
	mov ecx, 1024
210:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 210b
	mov eax, 6
	mov BYTE PTR [rbx+1440], al
	mov eax, 2
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 24576
	mov ecx, 1024
211:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 211b
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 3
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 5
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 6
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 28672
	mov ecx, 1024
212:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 212b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 4
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 4
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 4
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 32768
	mov ecx, 1024
213:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 213b
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 5
	mov BYTE PTR [rbx+1474], al
	mov eax, 4
	mov BYTE PTR [rbx+1475], al
	mov eax, 6
	mov BYTE PTR [rbx+1508], al
	mov eax, 4
	mov BYTE PTR [rbx+1509], al
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 36864
	mov ecx, 1024
214:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 214b
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 5
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 5
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 40960
	mov ecx, 1024
215:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 215b
	mov eax, 5
	mov BYTE PTR [rbx+1440], al
	mov eax, 5
	mov BYTE PTR [rbx+1441], al
	mov eax, 6
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 0
	mov BYTE PTR [rbx+1508], al
	mov eax, 6
	mov BYTE PTR [rbx+1509], al
	mov eax, 1
	mov BYTE PTR [rbx+1542], al
	mov eax, 6
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 45056
	mov ecx, 1024
216:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 216b
	mov eax, 2
	mov BYTE PTR [rbx+1440], al
	mov eax, 6
	mov BYTE PTR [rbx+1441], al
	mov eax, 3
	mov BYTE PTR [rbx+1474], al
	mov eax, 6
	mov BYTE PTR [rbx+1475], al
	mov eax, 4
	mov BYTE PTR [rbx+1508], al
	mov eax, 6
	mov BYTE PTR [rbx+1509], al
	mov eax, 5
	mov BYTE PTR [rbx+1542], al
	mov eax, 6
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 49152
	mov ecx, 1024
217:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 217b
	mov eax, 6
	mov BYTE PTR [rbx+1440], al
	mov eax, 6
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 7
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 7
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 7
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 53248
	mov ecx, 1024
218:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 218b
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 7
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
	mov BYTE PTR [rbx+1474], al
	mov eax, 7
	mov BYTE PTR [rbx+1475], al
	mov eax, 5
	mov BYTE PTR [rbx+1508], al
	mov eax, 7
	mov BYTE PTR [rbx+1509], al
	mov eax, 6
	mov BYTE PTR [rbx+1542], al
	mov eax, 7
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 57344
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4_avx512}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 57344
	mov ecx, 1024
219:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 219b
	mov eax, 0
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 61440
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 61440
	mov ecx, 256
220:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 220b
	mov eax, 1
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 62464
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 62464
	mov ecx, 256
221:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 221b
	mov eax, 2
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 63488
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 63488
	mov ecx, 256
222:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 222b
	mov eax, 3
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 64512
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 64512
	mov ecx, 256
223:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 223b
	mov eax, 4
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 65536
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 65536
	mov ecx, 256
224:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 224b
	mov eax, 5
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 66560
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 66560
	mov ecx, 256
225:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 225b
	mov eax, 6
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 67584
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 67584
	mov ecx, 256
226:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 226b
	mov eax, 7
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 68608
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 68608
	mov ecx, 256
227:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 227b
	mov eax, 8
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 69632
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 69632
	mov ecx, 256
228:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 228b
	mov eax, 9
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 70656
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 70656
	mov ecx, 256
229:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 229b
	mov eax, 10
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 71680
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 71680
	mov ecx, 256
230:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 230b
	mov eax, 11
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 72704
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 72704
	mov ecx, 256
231:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 231b
	mov eax, 12
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 73728
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 73728
	mov ecx, 256
232:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 232b
	mov eax, 13
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 74752
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 74752
	mov ecx, 256
233:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 233b
	mov eax, 14
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 75776
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 75776
	mov ecx, 256
234:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 234b
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
235:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 235b
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
236:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 236b
	mov rdi, r13
	add rdi, 32
	mov rsi, rbx
	add rsi, 1120
	mov ecx, 4
237:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 237b
	mov rdi, rbx
	add rdi, 61440
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 128
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 62464
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 224
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 63488
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 320
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 64512
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 416
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 65536
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 512
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 66560
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 608
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 67584
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 704
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 68608
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 800
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 69632
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 896
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 70656
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 992
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 71680
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1088
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 72704
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1184
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 73728
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1280
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 74752
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1376
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 75776
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1472
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 61440
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 62464
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 63488
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 64512
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 65536
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 66560
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 67584
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 6144
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 7168
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 9216
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 10240
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 68608
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 32
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1568
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 11264
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 13312
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 14336
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 15360
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 17408
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 69632
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 352
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1984
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 18432
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 19456
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 21504
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 22528
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 70656
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 672
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2400
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 25600
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 26624
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 27648
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 30720
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 31744
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 71680
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 992
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2816
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 34816
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 35840
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 37888
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 72704
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1312
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3232
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 39936
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 41984
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 44032
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 46080
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 73728
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1632
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3648
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 48128
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 50176
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 52224
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 74752
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1952
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 4064
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 54272
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 55296
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 56320
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 57344
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 58368
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 59392
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 60416
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_montgomery_multiply_add_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_montgomery_inv_ntt_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 75776
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 2272
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 4480
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
	mov r8d, 2592
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 8
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

vg_mldsa87_prepare_verifying_key_avx512:
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
	add rsi, 2592
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2592
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 3616
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 3616
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 4640
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4640
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 5664
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 5664
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1312
	mov rsi, rbx
	add rsi, 6688
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 6688
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1632
	mov rsi, rbx
	add rsi, 7712
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 7712
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1952
	mov rsi, rbx
	add rsi, 8736
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 8736
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 2272
	mov rsi, rbx
	add rsi, 9760
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 9760
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 324
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
	ret
	.p2align 6

vg_mldsa87_prepare_signing_key_avx512:
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
	add r8, 4896
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4896
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 5920
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5920
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 6944
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6944
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 7968
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7968
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 8992
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8992
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 10016
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10016
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 11040
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11040
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 12064
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12064
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 896
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 13088
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13088
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 992
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 14112
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 14112
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1088
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 15136
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 15136
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1184
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 16160
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16160
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 17184
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17184
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1376
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 18208
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18208
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1472
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 19232
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19232
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1568
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 20256
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20256
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1984
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 21280
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 21280
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 2400
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 22304
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 22304
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 2816
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 23328
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 23328
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 3232
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 24352
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 24352
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 3648
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 25376
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 25376
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 4064
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 26400
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 26400
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 4480
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 27424
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 27424
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 612
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
	ret
	.p2align 6

vg_mldsa87_sign_avx512:
	mov r9d, 0
	call {vg_mldsa87_sign_with_cache_avx512}
	ret
	.p2align 6

vg_mldsa87_sign_message_avx512:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 0
	call {vg_mldsa87_sign_with_cache_avx512}
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

vg_mldsa87_sign_message_prepared_avx512:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 1
	call {vg_mldsa87_sign_with_cache_avx512}
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

vg_mldsa87_verify_avx512:
	mov r8d, 0
	call {vg_mldsa87_verify_with_cache_avx512}
	ret
	.p2align 6

vg_mldsa87_verify_message_cached_avx512:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 0
	call {vg_mldsa87_verify_with_cache_avx512}
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

vg_mldsa87_verify_message_prepared_avx512:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 1
	call {vg_mldsa87_verify_with_cache_avx512}
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

vg_mldsa87_keygen:
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
	mov eax, 8
	mov BYTE PTR [rbx+896], al
	mov eax, 7
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
	add rdx, 79872
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
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 0
	mov BYTE PTR [rbx+1441], al
	mov eax, 5
	mov BYTE PTR [rbx+1474], al
	mov eax, 0
	mov BYTE PTR [rbx+1475], al
	mov eax, 6
	mov BYTE PTR [rbx+1508], al
	mov eax, 0
	mov BYTE PTR [rbx+1509], al
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 1
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 5
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 6
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 0
	mov BYTE PTR [rbx+1508], al
	mov eax, 2
	mov BYTE PTR [rbx+1509], al
	mov eax, 1
	mov BYTE PTR [rbx+1542], al
	mov eax, 2
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 79872
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
	mov eax, 2
	mov BYTE PTR [rbx+1440], al
	mov eax, 2
	mov BYTE PTR [rbx+1441], al
	mov eax, 3
	mov BYTE PTR [rbx+1474], al
	mov eax, 2
	mov BYTE PTR [rbx+1475], al
	mov eax, 4
	mov BYTE PTR [rbx+1508], al
	mov eax, 2
	mov BYTE PTR [rbx+1509], al
	mov eax, 5
	mov BYTE PTR [rbx+1542], al
	mov eax, 2
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 20480
	mov ecx, 1024
210:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 210b
	mov eax, 6
	mov BYTE PTR [rbx+1440], al
	mov eax, 2
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 24576
	mov ecx, 1024
211:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 211b
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 3
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 5
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 6
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 28672
	mov ecx, 1024
212:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 212b
	mov eax, 0
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 1
	mov BYTE PTR [rbx+1474], al
	mov eax, 4
	mov BYTE PTR [rbx+1475], al
	mov eax, 2
	mov BYTE PTR [rbx+1508], al
	mov eax, 4
	mov BYTE PTR [rbx+1509], al
	mov eax, 3
	mov BYTE PTR [rbx+1542], al
	mov eax, 4
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 32768
	mov ecx, 1024
213:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 213b
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 5
	mov BYTE PTR [rbx+1474], al
	mov eax, 4
	mov BYTE PTR [rbx+1475], al
	mov eax, 6
	mov BYTE PTR [rbx+1508], al
	mov eax, 4
	mov BYTE PTR [rbx+1509], al
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 36864
	mov ecx, 1024
214:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 214b
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 5
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 5
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 40960
	mov ecx, 1024
215:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 215b
	mov eax, 5
	mov BYTE PTR [rbx+1440], al
	mov eax, 5
	mov BYTE PTR [rbx+1441], al
	mov eax, 6
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 0
	mov BYTE PTR [rbx+1508], al
	mov eax, 6
	mov BYTE PTR [rbx+1509], al
	mov eax, 1
	mov BYTE PTR [rbx+1542], al
	mov eax, 6
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 45056
	mov ecx, 1024
216:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 216b
	mov eax, 2
	mov BYTE PTR [rbx+1440], al
	mov eax, 6
	mov BYTE PTR [rbx+1441], al
	mov eax, 3
	mov BYTE PTR [rbx+1474], al
	mov eax, 6
	mov BYTE PTR [rbx+1475], al
	mov eax, 4
	mov BYTE PTR [rbx+1508], al
	mov eax, 6
	mov BYTE PTR [rbx+1509], al
	mov eax, 5
	mov BYTE PTR [rbx+1542], al
	mov eax, 6
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 49152
	mov ecx, 1024
217:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 217b
	mov eax, 6
	mov BYTE PTR [rbx+1440], al
	mov eax, 6
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 7
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 7
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 7
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 53248
	mov ecx, 1024
218:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 218b
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 7
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
	mov BYTE PTR [rbx+1474], al
	mov eax, 7
	mov BYTE PTR [rbx+1475], al
	mov eax, 5
	mov BYTE PTR [rbx+1508], al
	mov eax, 7
	mov BYTE PTR [rbx+1509], al
	mov eax, 6
	mov BYTE PTR [rbx+1542], al
	mov eax, 7
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 57344
	mov rdx, rbx
	add rdx, 79872
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 57344
	mov ecx, 1024
219:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 219b
	mov eax, 0
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 61440
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 61440
	mov ecx, 256
220:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 220b
	mov eax, 1
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 62464
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 62464
	mov ecx, 256
221:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 221b
	mov eax, 2
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 63488
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 63488
	mov ecx, 256
222:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 222b
	mov eax, 3
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 64512
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 64512
	mov ecx, 256
223:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 223b
	mov eax, 4
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 65536
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 65536
	mov ecx, 256
224:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 224b
	mov eax, 5
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 66560
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 66560
	mov ecx, 256
225:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 225b
	mov eax, 6
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 67584
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 67584
	mov ecx, 256
226:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 226b
	mov eax, 7
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 68608
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 68608
	mov ecx, 256
227:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 227b
	mov eax, 8
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 69632
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 69632
	mov ecx, 256
228:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 228b
	mov eax, 9
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 70656
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 70656
	mov ecx, 256
229:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 229b
	mov eax, 10
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 71680
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 71680
	mov ecx, 256
230:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 230b
	mov eax, 11
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 72704
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 72704
	mov ecx, 256
231:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 231b
	mov eax, 12
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 73728
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 73728
	mov ecx, 256
232:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 232b
	mov eax, 13
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 74752
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 74752
	mov ecx, 256
233:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 233b
	mov eax, 14
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 2
	mov rdx, rbx
	add rdx, 75776
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 75776
	mov ecx, 256
234:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 234b
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
235:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 235b
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
236:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 236b
	mov rdi, r13
	add rdi, 32
	mov rsi, rbx
	add rsi, 1120
	mov ecx, 4
237:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 237b
	mov rdi, rbx
	add rdi, 61440
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 128
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 62464
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 224
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 63488
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 320
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 64512
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 416
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 65536
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 512
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 66560
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 608
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 67584
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 704
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 68608
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 800
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 69632
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 896
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 70656
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 992
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 71680
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1088
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 72704
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1184
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 73728
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1280
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 74752
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1376
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 75776
	mov esi, 2
	mov edx, 2
	mov rcx, r13
	add rcx, 1472
	mov r8d, 96
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 61440
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 62464
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 63488
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 64512
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 65536
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 66560
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 67584
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 6144
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 7168
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 9216
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 10240
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 68608
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 32
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1568
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 11264
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 12288
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 13312
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 14336
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 15360
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 17408
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 69632
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 352
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1984
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 18432
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 19456
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 21504
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 22528
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 23552
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 70656
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 672
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2400
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 25600
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 26624
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 27648
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 30720
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 31744
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 71680
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 992
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2816
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 34816
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 35840
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 37888
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 72704
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1312
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3232
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 39936
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 41984
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 43008
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 44032
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 46080
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 73728
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1632
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3648
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 48128
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 50176
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 52224
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 74752
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 1952
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 4064
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 54272
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 55296
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 56320
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 57344
	mov rdx, rbx
	add rdx, 64512
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 58368
	mov rdx, rbx
	add rdx, 65536
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 59392
	mov rdx, rbx
	add rdx, 66560
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 60416
	mov rdx, rbx
	add rdx, 67584
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_inv_ntt}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 75776
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 76800
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 78848
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 77824
	mov esi, 1023
	mov rdx, r12
	add rdx, 2272
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 78848
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 4480
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
	mov r8d, 2592
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 8
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

vg_mldsa87_prepare_verifying_key:
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
	add rsi, 2592
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2592
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 3616
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 3616
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 4640
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4640
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 5664
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 5664
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1312
	mov rsi, rbx
	add rsi, 6688
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 6688
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1632
	mov rsi, rbx
	add rsi, 7712
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 7712
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1952
	mov rsi, rbx
	add rsi, 8736
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 8736
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2272
	mov rsi, rbx
	add rsi, 9760
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 9760
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 324
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
	ret
	.p2align 6

vg_mldsa87_prepare_signing_key:
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
	add r8, 4896
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4896
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 224
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 5920
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5920
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 320
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 6944
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6944
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 416
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 7968
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7968
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 512
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 8992
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8992
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 608
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 10016
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10016
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 704
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 11040
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11040
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 800
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 12064
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12064
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 896
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 13088
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13088
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 992
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 14112
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 14112
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1088
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 15136
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 15136
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1184
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 16160
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16160
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 17184
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17184
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1376
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 18208
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18208
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1472
	mov esi, 96
	mov edx, 2
	mov ecx, 2
	mov r8, rbx
	add r8, 19232
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19232
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1568
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 20256
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20256
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1984
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 21280
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 21280
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2400
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 22304
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 22304
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2816
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 23328
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 23328
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 3232
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 24352
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 24352
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 3648
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 25376
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 25376
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 4064
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 26400
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 26400
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 4480
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 27424
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 27424
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 612
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
	ret
	.p2align 6

vg_mldsa87_sign:
	mov r9d, 0
	call {vg_mldsa87_sign_with_cache}
	ret
	.p2align 6

vg_mldsa87_sign_message:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 0
	call {vg_mldsa87_sign_with_cache}
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

vg_mldsa87_sign_message_prepared:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 1
	call {vg_mldsa87_sign_with_cache}
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

vg_mldsa87_verify:
	mov r8d, 0
	call {vg_mldsa87_verify_with_cache}
	ret
	.p2align 6

vg_mldsa87_verify_message_cached:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 0
	call {vg_mldsa87_verify_with_cache}
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

vg_mldsa87_verify_message_prepared:
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
	add rdi, 144384
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
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 144584
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 144384
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 145224
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 144584
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 145224
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 1
	call {vg_mldsa87_verify_with_cache}
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
