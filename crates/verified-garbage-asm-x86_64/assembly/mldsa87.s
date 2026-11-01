// The functions of `src/mldsa87.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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

vg_mldsa87_sign_avx2:
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
	add rsi, 64512
	mov rdx, rbx
	add rdx, 121856
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	add r8, 40960
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 40960
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	call {vg_mldsa_ntt_avx2}
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
	mov esi, 524288
	mov rdx, rbx
	add rdx, 18432
	mov rcx, rbx
	add rcx, 121856
	call {vg_mldsa_expand_mask_poly4_avx2}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 18432
	mov ecx, 128
212:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 212b
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 19456
	mov ecx, 128
213:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 213b
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 20480
	mov ecx, 128
214:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 214b
	mov rdi, rbx
	add rdi, 27648
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 21504
	mov ecx, 128
215:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 215b
	mov rdi, rbx
	add rdi, 28672
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 1296
	mov rsi, rbx
	add rsi, 960
	mov ecx, 8
216:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 216b
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
217:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 217b
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
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 218b
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
219:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 219b
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
	call {vg_mldsa_expand_mask_poly4_avx2}
	mov rdi, rbx
	add rdi, 22528
	mov rsi, rbx
	add rsi, 6144
	mov ecx, 128
220:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 220b
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 22528
	mov ecx, 128
221:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 221b
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 23552
	mov rsi, rbx
	add rsi, 7168
	mov ecx, 128
222:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 222b
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 23552
	mov ecx, 128
223:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 223b
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 24576
	mov rsi, rbx
	add rsi, 8192
	mov ecx, 128
224:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 224b
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 24576
	mov ecx, 128
225:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 225b
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 64512
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7_avx2}
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 71680
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7_avx2}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 78848
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7_avx2}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 86016
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7_avx2}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 93184
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7_avx2}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 100352
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7_avx2}
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 107520
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7_avx2}
	mov rdi, rbx
	add rdi, 39936
	mov rsi, rbx
	add rsi, 114688
	mov rdx, rbx
	add rdx, 25600
	mov rcx, rbx
	add rcx, 3072
	call {vg_mldsa_dot_inverse7_avx2}
	mov rdi, rbx
	add rdi, 32768
	mov esi, 261888
	mov rdx, rbx
	add rdx, 6144
	call {vg_mldsa_high_bits_avx2}
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
	call {vg_mldsa_high_bits_avx2}
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
	call {vg_mldsa_high_bits_avx2}
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
	call {vg_mldsa_high_bits_avx2}
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
	call {vg_mldsa_high_bits_avx2}
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
	call {vg_mldsa_high_bits_avx2}
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
	call {vg_mldsa_high_bits_avx2}
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
	call {vg_mldsa_high_bits_avx2}
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
	jne 226f
	mov r15d, 0
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
	jmp 227f
226:
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
	add rdx, 40960
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 18432
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 524168
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
	add rdx, 41984
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 19456
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 524168
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
	add rdx, 43008
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 20480
	mov esi, 524168
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
	add rdx, 44032
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 21504
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
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
	add rdx, 45056
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
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
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
	add rdx, 46080
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
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 23552
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
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
	add rdx, 47104
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
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 24576
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 240f
	jmp 241f
240:
241:
239:
237:
235:
233:
231:
229:
	test r15d, r15d
	jne 242f
	jmp 243f
242:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 32768
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 244f
	jmp 245f
244:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 49152
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 33792
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 246f
	jmp 247f
246:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 50176
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 34816
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 248f
	jmp 249f
248:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 51200
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 35840
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 250f
	jmp 251f
250:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 52224
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 36864
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 252f
	jmp 253f
252:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 53248
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 37888
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 254f
	jmp 255f
254:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 54272
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 38912
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 256f
	jmp 257f
256:
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 55296
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 6144
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 39936
	mov rsi, rbx
	add rsi, 6144
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 39936
	mov esi, 261888
	mov rdx, rbx
	add rdx, 7168
	call {vg_mldsa_low_bits_avx2}
	mov rdi, rbx
	add rdi, 7168
	mov esi, 261768
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	test r15d, r15d
	jne 258f
	jmp 259f
258:
259:
257:
255:
253:
251:
249:
247:
245:
	test r15d, r15d
	jne 260f
	jmp 261f
260:
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 56320
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 32768
	mov ecx, 128
262:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 262b
	mov rdi, rbx
	add rdi, 32768
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 32768
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 32768
	mov edx, 261888
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
	add rdx, 57344
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 33792
	mov ecx, 128
263:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 263b
	mov rdi, rbx
	add rdi, 33792
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 33792
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 33792
	mov edx, 261888
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
	add rdx, 58368
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 34816
	mov ecx, 128
264:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 264b
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 34816
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 34816
	mov edx, 261888
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
	add rdx, 59392
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 35840
	mov ecx, 128
265:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 265b
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 35840
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 35840
	mov edx, 261888
	mov rcx, rbx
	add rcx, 13312
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 60416
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 36864
	mov ecx, 128
266:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 266b
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 36864
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 36864
	mov edx, 261888
	mov rcx, rbx
	add rcx, 14336
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 61440
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 37888
	mov ecx, 128
267:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 267b
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 37888
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 37888
	mov edx, 261888
	mov rcx, rbx
	add rcx, 15360
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 62464
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 38912
	mov ecx, 128
268:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 268b
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 38912
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 38912
	mov edx, 261888
	mov rcx, rbx
	add rcx, 16384
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 5120
	mov rdx, rbx
	add rdx, 63488
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov rsi, rbx
	add rsi, 3072
	call {vg_mldsa_montgomery_inv_ntt_avx2}
	mov rdi, rbx
	add rdi, 8192
	mov esi, 261888
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 39936
	mov ecx, 128
269:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 269b
	mov rdi, rbx
	add rdi, 39936
	mov rsi, rbx
	add rsi, 8192
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 39936
	call {vg_mldsa_sub_avx2}
	mov rdi, rbx
	add rdi, 9216
	mov rsi, rbx
	add rsi, 39936
	mov edx, 261888
	mov rcx, rbx
	add rcx, 17408
	call {vg_mldsa_make_hint_avx2}
	mov ecx, DWORD PTR [rbx+904]
	add ecx, eax
	mov QWORD PTR [rbx+904], rcx
	mov eax, DWORD PTR [rbx+904]
	sub rax, 76
	shr rax, 63
	and r15d, eax
261:
243:
	test r15d, r15d
	jne 270f
	mov rax, QWORD PTR [rbx+896]
	add rax, 7
	mov QWORD PTR [rbx+896], rax
	jmp 271f
270:
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
271:
227:
	mov rax, QWORD PTR [rbx+888]
	sub rax, 1
	mov QWORD PTR [rbx+888], rax
	jne 27b
	test r15d, r15d
	jne 272f
	jmp 273f
272:
	mov rdi, r14
	add rdi, 0
	mov rsi, rbx
	add rsi, 1040
	mov ecx, 8
274:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 274b
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
273:
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
	call {vg_mldsa87_sign_avx2}
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
	add rdi, 4544
	mov esi, 83
	mov edx, 75
	mov rcx, rbx
	add rcx, 8192
	mov r8d, 2048
	call {vg_mldsa_hint_bit_unpack}
	mov r15d, eax
	test r15d, r15d
	jne 20f
	jmp 21f
20:
	mov rdi, r13
	add rdi, 64
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 16384
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 704
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 17408
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 1344
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 18432
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 1984
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 19456
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 2624
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 20480
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20480
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 3264
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 21504
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 21504
	mov esi, 524168
	call {vg_mldsa_norm_lt_avx2}
	and r15d, eax
	mov rdi, r13
	add rdi, 3904
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 22528
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 524168
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
	add rdx, 94208
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
	mov eax, 4
	mov BYTE PTR [rbx+2592], al
	mov eax, 0
	mov BYTE PTR [rbx+2593], al
	mov eax, 5
	mov BYTE PTR [rbx+2626], al
	mov eax, 0
	mov BYTE PTR [rbx+2627], al
	mov eax, 6
	mov BYTE PTR [rbx+2660], al
	mov eax, 0
	mov BYTE PTR [rbx+2661], al
	mov eax, 0
	mov BYTE PTR [rbx+2694], al
	mov eax, 1
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 94208
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
	mov eax, 1
	mov BYTE PTR [rbx+2592], al
	mov eax, 1
	mov BYTE PTR [rbx+2593], al
	mov eax, 2
	mov BYTE PTR [rbx+2626], al
	mov eax, 1
	mov BYTE PTR [rbx+2627], al
	mov eax, 3
	mov BYTE PTR [rbx+2660], al
	mov eax, 1
	mov BYTE PTR [rbx+2661], al
	mov eax, 4
	mov BYTE PTR [rbx+2694], al
	mov eax, 1
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 94208
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
	mov eax, 5
	mov BYTE PTR [rbx+2592], al
	mov eax, 1
	mov BYTE PTR [rbx+2593], al
	mov eax, 6
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
	add rsi, 40960
	mov rdx, rbx
	add rdx, 94208
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
	mov eax, 5
	mov BYTE PTR [rbx+2694], al
	mov eax, 2
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	mov eax, 6
	mov BYTE PTR [rbx+2592], al
	mov eax, 2
	mov BYTE PTR [rbx+2593], al
	mov eax, 0
	mov BYTE PTR [rbx+2626], al
	mov eax, 3
	mov BYTE PTR [rbx+2627], al
	mov eax, 1
	mov BYTE PTR [rbx+2660], al
	mov eax, 3
	mov BYTE PTR [rbx+2661], al
	mov eax, 2
	mov BYTE PTR [rbx+2694], al
	mov eax, 3
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	mov eax, 3
	mov BYTE PTR [rbx+2592], al
	mov eax, 3
	mov BYTE PTR [rbx+2593], al
	mov eax, 4
	mov BYTE PTR [rbx+2626], al
	mov eax, 3
	mov BYTE PTR [rbx+2627], al
	mov eax, 5
	mov BYTE PTR [rbx+2660], al
	mov eax, 3
	mov BYTE PTR [rbx+2661], al
	mov eax, 6
	mov BYTE PTR [rbx+2694], al
	mov eax, 3
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
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
	add rsi, 57344
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 57344
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
	mov eax, 4
	mov BYTE PTR [rbx+2592], al
	mov eax, 4
	mov BYTE PTR [rbx+2593], al
	mov eax, 5
	mov BYTE PTR [rbx+2626], al
	mov eax, 4
	mov BYTE PTR [rbx+2627], al
	mov eax, 6
	mov BYTE PTR [rbx+2660], al
	mov eax, 4
	mov BYTE PTR [rbx+2661], al
	mov eax, 0
	mov BYTE PTR [rbx+2694], al
	mov eax, 5
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 61440
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 61440
	mov ecx, 256
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
	add rsi, 65536
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 65536
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
218:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 218b
	mov eax, 5
	mov BYTE PTR [rbx+2592], al
	mov eax, 5
	mov BYTE PTR [rbx+2593], al
	mov eax, 6
	mov BYTE PTR [rbx+2626], al
	mov eax, 5
	mov BYTE PTR [rbx+2627], al
	mov eax, 0
	mov BYTE PTR [rbx+2660], al
	mov eax, 6
	mov BYTE PTR [rbx+2661], al
	mov eax, 1
	mov BYTE PTR [rbx+2694], al
	mov eax, 6
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 69632
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 69632
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
219:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 219b
	mov eax, 2
	mov BYTE PTR [rbx+2592], al
	mov eax, 6
	mov BYTE PTR [rbx+2593], al
	mov eax, 3
	mov BYTE PTR [rbx+2626], al
	mov eax, 6
	mov BYTE PTR [rbx+2627], al
	mov eax, 4
	mov BYTE PTR [rbx+2660], al
	mov eax, 6
	mov BYTE PTR [rbx+2661], al
	mov eax, 5
	mov BYTE PTR [rbx+2694], al
	mov eax, 6
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 73728
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 73728
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
220:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 220b
	mov eax, 6
	mov BYTE PTR [rbx+2592], al
	mov eax, 6
	mov BYTE PTR [rbx+2593], al
	mov eax, 0
	mov BYTE PTR [rbx+2626], al
	mov eax, 7
	mov BYTE PTR [rbx+2627], al
	mov eax, 1
	mov BYTE PTR [rbx+2660], al
	mov eax, 7
	mov BYTE PTR [rbx+2661], al
	mov eax, 2
	mov BYTE PTR [rbx+2694], al
	mov eax, 7
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 77824
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
221:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov eax, 3
	mov BYTE PTR [rbx+2592], al
	mov eax, 7
	mov BYTE PTR [rbx+2593], al
	mov eax, 4
	mov BYTE PTR [rbx+2626], al
	mov eax, 7
	mov BYTE PTR [rbx+2627], al
	mov eax, 5
	mov BYTE PTR [rbx+2660], al
	mov eax, 7
	mov BYTE PTR [rbx+2661], al
	mov eax, 6
	mov BYTE PTR [rbx+2694], al
	mov eax, 7
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 81920
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4_avx2}
	and r15d, eax
	mov rdi, rbx
	add rdi, 81920
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
222:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 222b
	mov rdi, r13
	add rdi, 0
	mov esi, 64
	mov edx, 60
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
223:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 223b
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
	add rdi, 21504
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 22528
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
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 34816
	mov rdx, rbx
	add rdx, 22528
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
	add rsi, 35840
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 37888
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 39936
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 41984
	mov rdx, rbx
	add rdx, 22528
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
	add rsi, 43008
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 44032
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 46080
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 48128
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 22528
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
	add rsi, 50176
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 52224
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 54272
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 55296
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 56320
	mov rdx, rbx
	add rdx, 22528
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
	add rsi, 57344
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 58368
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 59392
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 60416
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 61440
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 62464
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 63488
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
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
	add rsi, 64512
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 65536
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 66560
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 67584
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 68608
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 69632
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 70656
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
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
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 71680
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 72704
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 73728
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 74752
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 75776
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 76800
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbp
	add rdi, 1952
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
	add rdi, 14336
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
	add rdx, 1792
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 78848
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_montgomery_multiply_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 79872
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 80896
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 81920
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 82944
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 83968
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 84992
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_montgomery_multiply_add_ntt_avx2}
	mov rdi, rbp
	add rdi, 2272
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
	add rdi, 15360
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
	add rdx, 1920
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
	add rcx, 2048
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 2048
	mov rdi, r13
	add rdi, 0
	mov ecx, 64
	mov edx, 0
224:
	movzx eax, BYTE PTR [rsi]
	movzx r8d, BYTE PTR [rdi]
	xor rax, r8
	or rdx, rax
	add rsi, 1
	add rdi, 1
	sub rcx, 1
	jne 224b
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
	call {vg_mldsa87_verify_avx2}
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

vg_mldsa87_sign:
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
212:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 212b
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
213:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 213b
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
214:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 214b
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
215:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 215b
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
216:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 216b
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
217:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 217b
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
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 218b
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
219:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 219b
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
220:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 220b
	mov rdi, rbx
	add rdi, 29696
	mov rsi, rbx
	add rsi, 22528
	mov ecx, 128
221:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 221b
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
222:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 222b
	mov rdi, rbx
	add rdi, 30720
	mov rsi, rbx
	add rsi, 23552
	mov ecx, 128
223:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 223b
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
224:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 224b
	mov rdi, rbx
	add rdi, 31744
	mov rsi, rbx
	add rsi, 24576
	mov ecx, 128
225:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 225b
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
	jne 226f
	mov r15d, 0
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
	jmp 227f
226:
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
	jne 228f
	jmp 229f
228:
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
	jne 230f
	jmp 231f
230:
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
	jne 232f
	jmp 233f
232:
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
	jne 234f
	jmp 235f
234:
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
	jne 236f
	jmp 237f
236:
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
	jne 238f
	jmp 239f
238:
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
	jne 240f
	jmp 241f
240:
241:
239:
237:
235:
233:
231:
229:
	test r15d, r15d
	jne 242f
	jmp 243f
242:
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
	jne 244f
	jmp 245f
244:
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
	jne 246f
	jmp 247f
246:
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
	jne 248f
	jmp 249f
248:
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
	jne 250f
	jmp 251f
250:
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
	jne 252f
	jmp 253f
252:
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
	jne 254f
	jmp 255f
254:
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
	jne 256f
	jmp 257f
256:
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
	jne 258f
	jmp 259f
258:
259:
257:
255:
253:
251:
249:
247:
245:
	test r15d, r15d
	jne 260f
	jmp 261f
260:
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
262:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 262b
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
263:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 263b
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
264:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 264b
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
265:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 265b
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
266:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 266b
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
267:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 267b
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
268:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 268b
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
269:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 269b
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
261:
243:
	test r15d, r15d
	jne 270f
	mov rax, QWORD PTR [rbx+896]
	add rax, 7
	mov QWORD PTR [rbx+896], rax
	jmp 271f
270:
	mov eax, 1
	mov QWORD PTR [rbx+888], rax
271:
227:
	mov rax, QWORD PTR [rbx+888]
	sub rax, 1
	mov QWORD PTR [rbx+888], rax
	jne 27b
	test r15d, r15d
	jne 272f
	jmp 273f
272:
	mov rdi, r14
	add rdi, 0
	mov rsi, rbx
	add rsi, 1040
	mov ecx, 8
274:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 274b
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
273:
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
	call {vg_mldsa87_sign}
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
	add rdi, 4544
	mov esi, 83
	mov edx, 75
	mov rcx, rbx
	add rcx, 8192
	mov r8d, 2048
	call {vg_mldsa_hint_bit_unpack}
	mov r15d, eax
	test r15d, r15d
	jne 20f
	jmp 21f
20:
	mov rdi, r13
	add rdi, 64
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 16384
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16384
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 704
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 17408
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17408
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 1344
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 18432
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18432
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 1984
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 19456
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19456
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 2624
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 20480
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20480
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 3264
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 21504
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 21504
	mov esi, 524168
	call {vg_mldsa_norm_lt}
	and r15d, eax
	mov rdi, r13
	add rdi, 3904
	mov esi, 640
	mov edx, 524287
	mov ecx, 524288
	mov r8, rbx
	add r8, 22528
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 22528
	mov esi, 524168
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
	add rdx, 94208
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
	mov eax, 4
	mov BYTE PTR [rbx+2592], al
	mov eax, 0
	mov BYTE PTR [rbx+2593], al
	mov eax, 5
	mov BYTE PTR [rbx+2626], al
	mov eax, 0
	mov BYTE PTR [rbx+2627], al
	mov eax, 6
	mov BYTE PTR [rbx+2660], al
	mov eax, 0
	mov BYTE PTR [rbx+2661], al
	mov eax, 0
	mov BYTE PTR [rbx+2694], al
	mov eax, 1
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 94208
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
	mov eax, 1
	mov BYTE PTR [rbx+2592], al
	mov eax, 1
	mov BYTE PTR [rbx+2593], al
	mov eax, 2
	mov BYTE PTR [rbx+2626], al
	mov eax, 1
	mov BYTE PTR [rbx+2627], al
	mov eax, 3
	mov BYTE PTR [rbx+2660], al
	mov eax, 1
	mov BYTE PTR [rbx+2661], al
	mov eax, 4
	mov BYTE PTR [rbx+2694], al
	mov eax, 1
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 94208
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
	mov eax, 5
	mov BYTE PTR [rbx+2592], al
	mov eax, 1
	mov BYTE PTR [rbx+2593], al
	mov eax, 6
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
	add rsi, 40960
	mov rdx, rbx
	add rdx, 94208
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
	mov eax, 5
	mov BYTE PTR [rbx+2694], al
	mov eax, 2
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
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
	mov eax, 6
	mov BYTE PTR [rbx+2592], al
	mov eax, 2
	mov BYTE PTR [rbx+2593], al
	mov eax, 0
	mov BYTE PTR [rbx+2626], al
	mov eax, 3
	mov BYTE PTR [rbx+2627], al
	mov eax, 1
	mov BYTE PTR [rbx+2660], al
	mov eax, 3
	mov BYTE PTR [rbx+2661], al
	mov eax, 2
	mov BYTE PTR [rbx+2694], al
	mov eax, 3
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
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
	mov eax, 3
	mov BYTE PTR [rbx+2592], al
	mov eax, 3
	mov BYTE PTR [rbx+2593], al
	mov eax, 4
	mov BYTE PTR [rbx+2626], al
	mov eax, 3
	mov BYTE PTR [rbx+2627], al
	mov eax, 5
	mov BYTE PTR [rbx+2660], al
	mov eax, 3
	mov BYTE PTR [rbx+2661], al
	mov eax, 6
	mov BYTE PTR [rbx+2694], al
	mov eax, 3
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
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
	add rsi, 57344
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov rdi, rbx
	add rdi, 57344
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
	mov eax, 4
	mov BYTE PTR [rbx+2592], al
	mov eax, 4
	mov BYTE PTR [rbx+2593], al
	mov eax, 5
	mov BYTE PTR [rbx+2626], al
	mov eax, 4
	mov BYTE PTR [rbx+2627], al
	mov eax, 6
	mov BYTE PTR [rbx+2660], al
	mov eax, 4
	mov BYTE PTR [rbx+2661], al
	mov eax, 0
	mov BYTE PTR [rbx+2694], al
	mov eax, 5
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 61440
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov rdi, rbx
	add rdi, 61440
	mov ecx, 256
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
	add rsi, 65536
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov rdi, rbx
	add rdi, 65536
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
218:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 218b
	mov eax, 5
	mov BYTE PTR [rbx+2592], al
	mov eax, 5
	mov BYTE PTR [rbx+2593], al
	mov eax, 6
	mov BYTE PTR [rbx+2626], al
	mov eax, 5
	mov BYTE PTR [rbx+2627], al
	mov eax, 0
	mov BYTE PTR [rbx+2660], al
	mov eax, 6
	mov BYTE PTR [rbx+2661], al
	mov eax, 1
	mov BYTE PTR [rbx+2694], al
	mov eax, 6
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 69632
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov rdi, rbx
	add rdi, 69632
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
219:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 219b
	mov eax, 2
	mov BYTE PTR [rbx+2592], al
	mov eax, 6
	mov BYTE PTR [rbx+2593], al
	mov eax, 3
	mov BYTE PTR [rbx+2626], al
	mov eax, 6
	mov BYTE PTR [rbx+2627], al
	mov eax, 4
	mov BYTE PTR [rbx+2660], al
	mov eax, 6
	mov BYTE PTR [rbx+2661], al
	mov eax, 5
	mov BYTE PTR [rbx+2694], al
	mov eax, 6
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 73728
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov rdi, rbx
	add rdi, 73728
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
220:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 220b
	mov eax, 6
	mov BYTE PTR [rbx+2592], al
	mov eax, 6
	mov BYTE PTR [rbx+2593], al
	mov eax, 0
	mov BYTE PTR [rbx+2626], al
	mov eax, 7
	mov BYTE PTR [rbx+2627], al
	mov eax, 1
	mov BYTE PTR [rbx+2660], al
	mov eax, 7
	mov BYTE PTR [rbx+2661], al
	mov eax, 2
	mov BYTE PTR [rbx+2694], al
	mov eax, 7
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov rdi, rbx
	add rdi, 77824
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
221:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov eax, 3
	mov BYTE PTR [rbx+2592], al
	mov eax, 7
	mov BYTE PTR [rbx+2593], al
	mov eax, 4
	mov BYTE PTR [rbx+2626], al
	mov eax, 7
	mov BYTE PTR [rbx+2627], al
	mov eax, 5
	mov BYTE PTR [rbx+2660], al
	mov eax, 7
	mov BYTE PTR [rbx+2661], al
	mov eax, 6
	mov BYTE PTR [rbx+2694], al
	mov eax, 7
	mov BYTE PTR [rbx+2695], al
	mov rdi, rbx
	add rdi, 2560
	mov rsi, rbx
	add rsi, 81920
	mov rdx, rbx
	add rdx, 94208
	call {vg_mldsa_rej_ntt_poly4}
	and r15d, eax
	mov rdi, rbx
	add rdi, 81920
	mov ecx, 256
	mov edx, 0
	sub edx, eax
	movq xmm0, rdx
	pshufd xmm0, xmm0, 0
222:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 222b
	mov rdi, r13
	add rdi, 0
	mov esi, 64
	mov edx, 60
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
223:
	movdqu xmm1, XMMWORD PTR [rdi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [rdi], xmm1
	add rdi, 16
	sub rcx, 1
	jne 223b
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
	add rdi, 20480
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 21504
	mov rsi, rbx
	add rsi, 4096
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 22528
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
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 34816
	mov rdx, rbx
	add rdx, 22528
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
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
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
	add rsi, 35840
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 36864
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 37888
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 38912
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 39936
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 40960
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 41984
	mov rdx, rbx
	add rdx, 22528
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
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
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
	add rsi, 43008
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 44032
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 45056
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 46080
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 48128
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 49152
	mov rdx, rbx
	add rdx, 22528
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
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
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
	add rsi, 50176
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 51200
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 52224
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 53248
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 54272
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 55296
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 56320
	mov rdx, rbx
	add rdx, 22528
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
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
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
	add rsi, 57344
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 58368
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 59392
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 60416
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 61440
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 62464
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 63488
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbp
	add rdi, 1312
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
	add rdi, 12288
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
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
	add rsi, 64512
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 65536
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 66560
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 67584
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 68608
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 69632
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 70656
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbp
	add rdi, 1632
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
	add rdi, 13312
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1664
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 71680
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 72704
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 73728
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 74752
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 75776
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 76800
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 77824
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbp
	add rdi, 1952
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
	add rdi, 14336
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1792
	mov ecx, 128
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 78848
	mov rdx, rbx
	add rdx, 16384
	call {vg_mldsa_multiply_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 79872
	mov rdx, rbx
	add rdx, 17408
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 80896
	mov rdx, rbx
	add rdx, 18432
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 81920
	mov rdx, rbx
	add rdx, 19456
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 82944
	mov rdx, rbx
	add rdx, 20480
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 83968
	mov rdx, rbx
	add rdx, 21504
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbx
	add rdi, 26624
	mov rsi, rbx
	add rsi, 84992
	mov rdx, rbx
	add rdx, 22528
	call {vg_mldsa_multiply_add_ntt}
	mov rdi, rbp
	add rdi, 2272
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
	add rdi, 15360
	mov rsi, rbx
	add rsi, 26624
	mov edx, 261888
	mov rcx, rbx
	add rcx, 27648
	call {vg_mldsa_use_hint}
	mov rdi, rbx
	add rdi, 27648
	mov esi, 15
	mov rdx, rbx
	add rdx, 1920
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
	add rcx, 2048
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 2048
	mov rdi, r13
	add rdi, 0
	mov ecx, 64
	mov edx, 0
224:
	movzx eax, BYTE PTR [rsi]
	movzx r8d, BYTE PTR [rdi]
	xor rax, r8
	or rdx, rax
	add rsi, 1
	add rdi, 1
	sub rcx, 1
	jne 224b
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
	call {vg_mldsa87_verify}
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
