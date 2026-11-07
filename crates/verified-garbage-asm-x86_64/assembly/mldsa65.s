// The functions of `src/mldsa65.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_pk_tr:
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
	mov r8d, 1952
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 48
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

vg_mldsa65_keygen_avx2:
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
	mov eax, 6
	mov BYTE PTR [rbx+896], al
	mov eax, 5
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
	add rdx, 49152
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
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 1
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
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
	add rsi, 12288
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 3
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 49152
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
	add rsi, 24576
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 5
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 3
	mov BYTE PTR [rbx+1184], al
	mov eax, 5
	mov BYTE PTR [rbx+1185], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 2048
	call {vg_mldsa_rej_ntt_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 32768
	mov ecx, 256
213:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 213b
	mov eax, 4
	mov BYTE PTR [rbx+1184], al
	mov eax, 5
	mov BYTE PTR [rbx+1185], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 2048
	call {vg_mldsa_rej_ntt_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 33792
	mov ecx, 256
214:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 214b
	mov eax, 0
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 34816
	mov ecx, 256
215:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 215b
	mov eax, 1
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 35840
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 35840
	mov ecx, 256
216:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 216b
	mov eax, 2
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 36864
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 36864
	mov ecx, 256
217:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 217b
	mov eax, 3
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 37888
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 37888
	mov ecx, 256
218:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 218b
	mov eax, 4
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 38912
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 38912
	mov ecx, 256
219:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 219b
	mov eax, 5
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 39936
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 39936
	mov ecx, 256
220:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 220b
	mov eax, 6
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 40960
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 40960
	mov ecx, 256
221:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 221b
	mov eax, 7
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 41984
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 41984
	mov ecx, 256
222:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 222b
	mov eax, 8
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 43008
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 43008
	mov ecx, 256
223:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 223b
	mov eax, 9
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 44032
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 44032
	mov ecx, 256
224:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 224b
	mov eax, 10
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 45056
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 45056
	mov ecx, 256
225:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 225b
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
226:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 226b
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 227b
	mov rdi, r13
	add rdi, 32
	mov rsi, rbx
	add rsi, 1120
	mov ecx, 4
228:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 228b
	mov rdi, rbx
	add rdi, 34816
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 128
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 35840
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 256
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 36864
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 384
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 37888
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 512
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 38912
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 640
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 39936
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 768
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 40960
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 896
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 41984
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1024
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 43008
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1152
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 44032
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1280
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 45056
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1408
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 39936
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 32
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1536
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 9216
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 40960
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 352
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1952
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 14336
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 41984
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 672
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2368
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 19456
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 43008
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 992
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2784
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 44032
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 1312
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3200
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 45056
	call {vg_mldsa_add_avx2}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 1632
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3616
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
	mov r8d, 1952
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 48
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

vg_mldsa65_prepare_verifying_key_avx2:
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
	add rsi, 1952
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 1952
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 2976
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2976
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 4000
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4000
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 5024
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 5024
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1312
	mov rsi, rbx
	add rsi, 6048
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 6048
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1632
	mov rsi, rbx
	add rsi, 7072
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 7072
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 244
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

vg_mldsa65_prepare_signing_key_avx2:
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
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 4032
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4032
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 256
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 5056
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5056
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 384
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 6080
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6080
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 512
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 7104
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7104
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 640
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 8128
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8128
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 768
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 9152
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 9152
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 896
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 10176
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10176
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1024
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 11200
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11200
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1152
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 12224
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12224
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 13248
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13248
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1408
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 14272
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 14272
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1536
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 15296
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 15296
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 1952
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 16320
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16320
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2368
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 17344
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17344
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 2784
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 18368
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18368
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 3200
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 19392
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19392
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbp
	add rdi, 3616
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 20416
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20416
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx2}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 504
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

vg_mldsa65_sign_avx2:
	mov r9d, 0
	call {vg_mldsa65_sign_with_cache_avx2}
	ret
	.p2align 6

vg_mldsa65_sign_message_avx2:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 0
	call {vg_mldsa65_sign_with_cache_avx2}
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

vg_mldsa65_sign_message_prepared_avx2:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 1
	call {vg_mldsa65_sign_with_cache_avx2}
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

vg_mldsa65_verify_avx2:
	mov r8d, 0
	call {vg_mldsa65_verify_with_cache_avx2}
	ret
	.p2align 6

vg_mldsa65_verify_message_cached_avx2:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 0
	call {vg_mldsa65_verify_with_cache_avx2}
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

vg_mldsa65_verify_message_prepared_avx2:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 1
	call {vg_mldsa65_verify_with_cache_avx2}
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

vg_mldsa65_keygen_avx512:
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
	mov eax, 6
	mov BYTE PTR [rbx+896], al
	mov eax, 5
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
	add rdx, 49152
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
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 1
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
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
	add rsi, 12288
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 3
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 49152
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
	add rsi, 24576
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 5
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 3
	mov BYTE PTR [rbx+1184], al
	mov eax, 5
	mov BYTE PTR [rbx+1185], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 2048
	call {vg_mldsa_rej_ntt_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 32768
	mov ecx, 256
213:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 213b
	mov eax, 4
	mov BYTE PTR [rbx+1184], al
	mov eax, 5
	mov BYTE PTR [rbx+1185], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 2048
	call {vg_mldsa_rej_ntt_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 33792
	mov ecx, 256
214:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 214b
	mov eax, 0
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 34816
	mov ecx, 256
215:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 215b
	mov eax, 1
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 35840
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 35840
	mov ecx, 256
216:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 216b
	mov eax, 2
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 36864
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 36864
	mov ecx, 256
217:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 217b
	mov eax, 3
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 37888
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 37888
	mov ecx, 256
218:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 218b
	mov eax, 4
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 38912
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 38912
	mov ecx, 256
219:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 219b
	mov eax, 5
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 39936
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 39936
	mov ecx, 256
220:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 220b
	mov eax, 6
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 40960
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 40960
	mov ecx, 256
221:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 221b
	mov eax, 7
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 41984
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 41984
	mov ecx, 256
222:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 222b
	mov eax, 8
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 43008
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 43008
	mov ecx, 256
223:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 223b
	mov eax, 9
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 44032
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 44032
	mov ecx, 256
224:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 224b
	mov eax, 10
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 45056
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 45056
	mov ecx, 256
225:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 225b
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
226:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 226b
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 227b
	mov rdi, r13
	add rdi, 32
	mov rsi, rbx
	add rsi, 1120
	mov ecx, 4
228:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 228b
	mov rdi, rbx
	add rdi, 34816
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 128
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 35840
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 256
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 36864
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 384
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 37888
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 512
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 38912
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 640
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 39936
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 768
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 40960
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 896
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 41984
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1024
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 43008
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1152
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 44032
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1280
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 45056
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1408
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 39936
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 32
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1536
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 9216
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 40960
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 352
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1952
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 14336
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 41984
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 672
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2368
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 19456
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 43008
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 992
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2784
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 44032
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 1312
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3200
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 45056
	call {vg_mldsa_add_avx512}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 1632
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3616
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
	mov r8d, 1952
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 48
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

vg_mldsa65_prepare_verifying_key_avx512:
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
	add rsi, 1952
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 1952
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 2976
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2976
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 4000
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4000
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 5024
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 5024
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1312
	mov rsi, rbx
	add rsi, 6048
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 6048
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1632
	mov rsi, rbx
	add rsi, 7072
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 7072
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 244
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

vg_mldsa65_prepare_signing_key_avx512:
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
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 4032
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4032
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 256
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 5056
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5056
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 384
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 6080
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6080
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 512
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 7104
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7104
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 640
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 8128
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8128
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 768
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 9152
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 9152
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 896
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 10176
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10176
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1024
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 11200
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11200
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1152
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 12224
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12224
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 13248
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13248
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1408
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 14272
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 14272
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1536
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 15296
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 15296
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 1952
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 16320
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16320
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 2368
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 17344
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17344
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 2784
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 18368
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18368
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 3200
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 19392
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19392
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbp
	add rdi, 3616
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 20416
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20416
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt_avx512}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 504
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

vg_mldsa65_sign_avx512:
	mov r9d, 0
	call {vg_mldsa65_sign_with_cache_avx512}
	ret
	.p2align 6

vg_mldsa65_sign_message_avx512:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 0
	call {vg_mldsa65_sign_with_cache_avx512}
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

vg_mldsa65_sign_message_prepared_avx512:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 1
	call {vg_mldsa65_sign_with_cache_avx512}
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

vg_mldsa65_verify_avx512:
	mov r8d, 0
	call {vg_mldsa65_verify_with_cache_avx512}
	ret
	.p2align 6

vg_mldsa65_verify_message_cached_avx512:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 0
	call {vg_mldsa65_verify_with_cache_avx512}
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

vg_mldsa65_verify_message_prepared_avx512:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 1
	call {vg_mldsa65_verify_with_cache_avx512}
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

vg_mldsa65_keygen:
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
	mov eax, 6
	mov BYTE PTR [rbx+896], al
	mov eax, 5
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
	add rdx, 49152
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
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 1
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 1
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 1
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 3
	mov BYTE PTR [rbx+1440], al
	mov eax, 1
	mov BYTE PTR [rbx+1441], al
	mov eax, 4
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
	add rsi, 12288
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 0
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 16384
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 1
	mov BYTE PTR [rbx+1440], al
	mov eax, 3
	mov BYTE PTR [rbx+1441], al
	mov eax, 2
	mov BYTE PTR [rbx+1474], al
	mov eax, 3
	mov BYTE PTR [rbx+1475], al
	mov eax, 3
	mov BYTE PTR [rbx+1508], al
	mov eax, 3
	mov BYTE PTR [rbx+1509], al
	mov eax, 4
	mov BYTE PTR [rbx+1542], al
	mov eax, 3
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 49152
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
	add rsi, 24576
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 4
	mov BYTE PTR [rbx+1440], al
	mov eax, 4
	mov BYTE PTR [rbx+1441], al
	mov eax, 0
	mov BYTE PTR [rbx+1474], al
	mov eax, 5
	mov BYTE PTR [rbx+1475], al
	mov eax, 1
	mov BYTE PTR [rbx+1508], al
	mov eax, 5
	mov BYTE PTR [rbx+1509], al
	mov eax, 2
	mov BYTE PTR [rbx+1542], al
	mov eax, 5
	mov BYTE PTR [rbx+1543], al
	mov rdi, rbx
	add rdi, 1408
	mov rsi, rbx
	add rsi, 28672
	mov rdx, rbx
	add rdx, 49152
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
	mov eax, 3
	mov BYTE PTR [rbx+1184], al
	mov eax, 5
	mov BYTE PTR [rbx+1185], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 32768
	mov rdx, rbx
	add rdx, 2048
	call {vg_mldsa_rej_ntt_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 32768
	mov ecx, 256
213:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 213b
	mov eax, 4
	mov BYTE PTR [rbx+1184], al
	mov eax, 5
	mov BYTE PTR [rbx+1185], al
	mov rdi, rbx
	add rdi, 1152
	mov rsi, rbx
	add rsi, 33792
	mov rdx, rbx
	add rdx, 2048
	call {vg_mldsa_rej_ntt_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 33792
	mov ecx, 256
214:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 214b
	mov eax, 0
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 34816
	mov ecx, 256
215:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 215b
	mov eax, 1
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 35840
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 35840
	mov ecx, 256
216:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 216b
	mov eax, 2
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 36864
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 36864
	mov ecx, 256
217:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 217b
	mov eax, 3
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 37888
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 37888
	mov ecx, 256
218:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 218b
	mov eax, 4
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 38912
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 38912
	mov ecx, 256
219:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 219b
	mov eax, 5
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 39936
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 39936
	mov ecx, 256
220:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 220b
	mov eax, 6
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 40960
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 40960
	mov ecx, 256
221:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 221b
	mov eax, 7
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 41984
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 41984
	mov ecx, 256
222:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 222b
	mov eax, 8
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 43008
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 43008
	mov ecx, 256
223:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 223b
	mov eax, 9
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 44032
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 44032
	mov ecx, 256
224:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 224b
	mov eax, 10
	mov BYTE PTR [rbx+1280], al
	mov rdi, rbx
	add rdi, 1216
	mov esi, 4
	mov rdx, rbx
	add rdx, 45056
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_rej_bounded_poly}
	and r15d, eax
	mov r8d, 0
	sub r8d, eax
	mov rdi, rbx
	add rdi, 45056
	mov ecx, 256
225:
	mov eax, DWORD PTR [rdi]
	and eax, r8d
	mov DWORD PTR [rdi], eax
	add rdi, 4
	sub rcx, 1
	jne 225b
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
226:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 226b
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 227b
	mov rdi, r13
	add rdi, 32
	mov rsi, rbx
	add rsi, 1120
	mov ecx, 4
228:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 228b
	mov rdi, rbx
	add rdi, 34816
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 128
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 35840
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 256
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 36864
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 384
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 37888
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 512
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 38912
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 640
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 39936
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 768
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 40960
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 896
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 41984
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1024
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 43008
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1152
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 44032
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1280
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 45056
	mov esi, 4
	mov edx, 4
	mov rcx, r13
	add rcx, 1408
	mov r8d, 128
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 34816
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 35840
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 36864
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 37888
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 38912
	mov rsi, rbx
	add rsi, 2048
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 39936
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 32
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1536
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 9216
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 40960
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 352
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 1952
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 14336
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 41984
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 672
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2368
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 19456
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 43008
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 992
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 2784
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 24576
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 44032
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 1312
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3200
	mov r8d, 416
	call {vg_mldsa_bit_pack}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 29696
	mov rdx, rbx
	add rdx, 34816
	mov rcx, rbx
	add rcx, 2048
	call {vg_mldsa_dot_inverse5}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 45056
	call {vg_mldsa_add}
	mov rdi, rbx
	add rdi, 46080
	mov rsi, rbx
	add rsi, 47104
	mov rdx, rbx
	add rdx, 48128
	call {vg_mldsa_power2round}
	mov rdi, rbx
	add rdi, 47104
	mov esi, 1023
	mov rdx, r12
	add rdx, 1632
	mov ecx, 320
	call {vg_mldsa_simple_bit_pack}
	mov rdi, rbx
	add rdi, 48128
	mov esi, 4095
	mov edx, 4096
	mov rcx, r13
	add rcx, 3616
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
	mov r8d, 1952
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 48
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

vg_mldsa65_prepare_verifying_key:
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
	add rsi, 1952
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 1952
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 352
	mov rsi, rbx
	add rsi, 2976
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 2976
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 672
	mov rsi, rbx
	add rsi, 4000
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 4000
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 992
	mov rsi, rbx
	add rsi, 5024
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 5024
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1312
	mov rsi, rbx
	add rsi, 6048
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 6048
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1632
	mov rsi, rbx
	add rsi, 7072
	call {vg_mldsa_unpack_t1}
	mov rdi, rbx
	add rdi, 7072
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 244
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

vg_mldsa65_prepare_signing_key:
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
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 4032
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 4032
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 256
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 5056
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 5056
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 384
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 6080
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 6080
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 512
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 7104
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 7104
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 640
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 8128
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 8128
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 768
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 9152
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 9152
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 896
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 10176
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 10176
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1024
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 11200
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 11200
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1152
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 12224
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 12224
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1280
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 13248
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 13248
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1408
	mov esi, 128
	mov edx, 4
	mov ecx, 4
	mov r8, rbx
	add r8, 14272
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 14272
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1536
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 15296
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 15296
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 1952
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 16320
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 16320
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2368
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 17344
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 17344
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 2784
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 18368
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 18368
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 3200
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 19392
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 19392
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbp
	add rdi, 3616
	mov esi, 416
	mov edx, 4095
	mov ecx, 4096
	mov r8, rbx
	add r8, 20416
	call {vg_mldsa_bit_unpack}
	mov rdi, rbx
	add rdi, 20416
	mov rsi, rbx
	add rsi, 0
	call {vg_mldsa_ntt}
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbp
	add rsi, 0
	mov ecx, 504
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

vg_mldsa65_sign:
	mov r9d, 0
	call {vg_mldsa65_sign_with_cache}
	ret
	.p2align 6

vg_mldsa65_sign_message:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 0
	call {vg_mldsa65_sign_with_cache}
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

vg_mldsa65_sign_message_prepared:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 64
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+16]
	mov rcx, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [rsp+8]
	mov r9d, 1
	call {vg_mldsa65_sign_with_cache}
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

vg_mldsa65_verify:
	mov r8d, 0
	call {vg_mldsa65_verify_with_cache}
	ret
	.p2align 6

vg_mldsa65_verify_message_cached:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 0
	call {vg_mldsa65_verify_with_cache}
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

vg_mldsa65_verify_message_prepared:
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
	add rdi, 103424
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
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+16]
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 64
	mov rcx, rsp
	mov r8d, 2
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 66
	mov rcx, QWORD PTR [rsp+40]
	mov r8, QWORD PTR [rsp+32]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+8]
	add r8, 103624
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+8]
	add rdi, 103424
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+8]
	add rcx, 104264
	mov r8d, 64
	mov r9, QWORD PTR [rsp+8]
	add r9, 103624
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+8]
	add rsi, 104264
	mov rdx, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [rsp+8]
	mov r8d, 1
	call {vg_mldsa65_verify_with_cache}
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
