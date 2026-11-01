// The functions of `src/rsa_oaep_sha256_mgf1_sha1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_crt_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_adx}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_crt_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_ifma}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani_crt_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_adx}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani_crt_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_ifma}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_crt_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_adx}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_crt_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_ifma}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani_crt_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_adx}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani_crt_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_ifma}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_crt_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_adx}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_crt_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_ifma}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani_crt_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_adx}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani_crt_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_ifma}
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
22:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 23f
	jmp 24f
23:
	mov r10, rax
24:
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 25b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 22b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
26:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 27f
	jmp 28f
27:
	mov r10, rax
28:
	mov r8d, 0
29:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 29b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 26b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
210:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 210b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
211:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 211b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
212:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 212b
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
214:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 215b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 214b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 216b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
217:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_rsa_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_rsa_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_mgf1_shani_rsa_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_mgf1_shani:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_mgf1_shani_rsa_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_avx2_rsa_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_avx2:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_avx2_rsa_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_avx2_mgf1_shani_rsa_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_avx2_mgf1_shani:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_avx2_mgf1_shani_rsa_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_avx2}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_shani_rsa_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_shani:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_shani_rsa_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_shani_mgf1_shani_rsa_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_shani_mgf1_shani:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_shani_mgf1_shani_rsa_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 20f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 22f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
24:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 24b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
25:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha256_finalize_scratch_shani}
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
26:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 26b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 27f
29:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 29b
	jmp 28f
27:
28:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
210:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 211f
	jmp 212f
211:
	mov r10, rax
212:
	mov r8d, 0
213:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 213b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 210b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
214:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	call {vg_sha1_init}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	call {vg_sha1_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	call {vg_sha1_finalize_scratch_shani}
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10d, 20
	cmp rax, r10
	jb 215f
	jmp 216f
215:
	mov r10, rax
216:
	mov r8d, 0
217:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 217b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, 20
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 214b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+360]
	mov rcx, QWORD PTR [rsp+368]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
23:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6
