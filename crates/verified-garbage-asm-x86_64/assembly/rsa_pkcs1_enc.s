// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_decrypt_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_sha256_avx2_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_sha256_avx2:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_sha256_avx2_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_sha256_shani_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_sha256_shani:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_sha256_shani_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
	ret
	.p2align 6

vg_rsa_pkcs1_encrypt_precomputed_adx:
	lea rsp, [rsp-1112]
	mov r10, QWORD PTR [rsp+1152]
	mov r11, QWORD PTR [rsp+1160]
	mov rsi, QWORD PTR [rsp+1136]
	mov rax, QWORD PTR [rsp+1144]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rdx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], r8
	mov QWORD PTR [rsp+64], r9
	mov rdi, rsp
	add rdi, 80
	mov QWORD PTR [rsp], rdi
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov rcx, rax
	mov eax, 0
	mov BYTE PTR [rsp+80], al
	mov eax, 2
	mov BYTE PTR [rsp+81], al
	mov r10d, 0
	mov edx, 0
20:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rsp+r10*1+82], al
	cmp rax, 1
	sbb r11, r11
	or rdx, r11
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+1120]
	mov r11, QWORD PTR [rsp+1128]
	mov eax, 0
	mov BYTE PTR [rsp+rcx*1+82], al
	mov QWORD PTR [rsp+72], rdx
	mov rdi, rsp
	add rdi, rcx
	add rdi, 83
	mov rcx, r11
	mov r10d, 0
	test rcx, rcx
	jne 21f
	jmp 22f
21:
23:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 23b
22:
	mov rdi, QWORD PTR [rsp+32]
	mov rsi, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [rsp+40]
	mov rcx, QWORD PTR [rsp+48]
	mov r8, QWORD PTR [rsp+56]
	mov r9, QWORD PTR [rsp+64]
	mov rdx, QWORD PTR [rsp+1168]
	mov rcx, QWORD PTR [rsp+1176]
	call {vg_rsa_public_precomputed_checked_adx}
	mov rdx, QWORD PTR [rsp+72]
	xor rdx, -1
	and rax, rdx
	mov r11, rax
	mov rdi, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [rsp+48]
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rdi+r10*1]
	and rax, rdx
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+80], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rax, r11
	lea rsp, [rsp+1112]
	ret
	.p2align 6

vg_rsa_pkcs1_encrypt_precomputed:
	lea rsp, [rsp-1112]
	mov r10, QWORD PTR [rsp+1152]
	mov r11, QWORD PTR [rsp+1160]
	mov rsi, QWORD PTR [rsp+1136]
	mov rax, QWORD PTR [rsp+1144]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rdx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], r8
	mov QWORD PTR [rsp+64], r9
	mov rdi, rsp
	add rdi, 80
	mov QWORD PTR [rsp], rdi
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov rcx, rax
	mov eax, 0
	mov BYTE PTR [rsp+80], al
	mov eax, 2
	mov BYTE PTR [rsp+81], al
	mov r10d, 0
	mov edx, 0
20:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rsp+r10*1+82], al
	cmp rax, 1
	sbb r11, r11
	or rdx, r11
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+1120]
	mov r11, QWORD PTR [rsp+1128]
	mov eax, 0
	mov BYTE PTR [rsp+rcx*1+82], al
	mov QWORD PTR [rsp+72], rdx
	mov rdi, rsp
	add rdi, rcx
	add rdi, 83
	mov rcx, r11
	mov r10d, 0
	test rcx, rcx
	jne 21f
	jmp 22f
21:
23:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 23b
22:
	mov rdi, QWORD PTR [rsp+32]
	mov rsi, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [rsp+40]
	mov rcx, QWORD PTR [rsp+48]
	mov r8, QWORD PTR [rsp+56]
	mov r9, QWORD PTR [rsp+64]
	mov rdx, QWORD PTR [rsp+1168]
	mov rcx, QWORD PTR [rsp+1176]
	call {vg_rsa_public_precomputed_checked}
	mov rdx, QWORD PTR [rsp+72]
	xor rdx, -1
	and rax, rdx
	mov r11, rax
	mov rdi, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [rsp+48]
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rdi+r10*1]
	and rax, rdx
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+80], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rax, r11
	lea rsp, [rsp+1112]
	ret
	.p2align 6

vg_rsa_pkcs1_encrypt_precomputed_ifma:
	lea rsp, [rsp-1112]
	mov r10, QWORD PTR [rsp+1152]
	mov r11, QWORD PTR [rsp+1160]
	mov rsi, QWORD PTR [rsp+1136]
	mov rax, QWORD PTR [rsp+1144]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rdx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], r8
	mov QWORD PTR [rsp+64], r9
	mov rdi, rsp
	add rdi, 80
	mov QWORD PTR [rsp], rdi
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov rcx, rax
	mov eax, 0
	mov BYTE PTR [rsp+80], al
	mov eax, 2
	mov BYTE PTR [rsp+81], al
	mov r10d, 0
	mov edx, 0
20:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rsp+r10*1+82], al
	cmp rax, 1
	sbb r11, r11
	or rdx, r11
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+1120]
	mov r11, QWORD PTR [rsp+1128]
	mov eax, 0
	mov BYTE PTR [rsp+rcx*1+82], al
	mov QWORD PTR [rsp+72], rdx
	mov rdi, rsp
	add rdi, rcx
	add rdi, 83
	mov rcx, r11
	mov r10d, 0
	test rcx, rcx
	jne 21f
	jmp 22f
21:
23:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 23b
22:
	mov rdi, QWORD PTR [rsp+32]
	mov rsi, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [rsp+40]
	mov rcx, QWORD PTR [rsp+48]
	mov r8, QWORD PTR [rsp+56]
	mov r9, QWORD PTR [rsp+64]
	mov rdx, QWORD PTR [rsp+1168]
	mov rcx, QWORD PTR [rsp+1176]
	call {vg_rsa_public_precomputed_checked_ifma}
	mov rdx, QWORD PTR [rsp+72]
	xor rdx, -1
	and rax, rdx
	mov r11, rax
	mov rdi, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [rsp+48]
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rdi+r10*1]
	and rax, rdx
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+80], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rax, r11
	lea rsp, [rsp+1112]
	ret
	.p2align 6
