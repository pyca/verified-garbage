// The functions of `src/ecdsa_secp256k1_sha256.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_secp256k1_sha256_sign:
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rsp+64], rax
	movabs rdx, -4624529908474429119
	sub rax, rdx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rsp+72], rax
	movabs rdx, -4994812053365940165
	sbb rax, rdx
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rsp+80], rax
	movabs rdx, -2
	sbb rax, rdx
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rsp+88], rax
	movabs rdx, -1
	sbb rax, rdx
	mov QWORD PTR [rsp+24], rax
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+8]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+144], rax
	mov rax, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+16]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+136], rax
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+24]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+128], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 161
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 1
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 161
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 8
	mov QWORD PTR [rsp+176], rax
20:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_secp256k1_sign}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 21f
	xor edx, edx
	jmp 22f
21:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 33
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 97
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch}
	mov edx, 1
	test rdx, rdx
22:
	jne 20b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	ret
	.p2align 6

vg_ecdsa_secp256k1_sha256_sign_avx2:
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rsp+64], rax
	movabs rdx, -4624529908474429119
	sub rax, rdx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rsp+72], rax
	movabs rdx, -4994812053365940165
	sbb rax, rdx
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rsp+80], rax
	movabs rdx, -2
	sbb rax, rdx
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rsp+88], rax
	movabs rdx, -1
	sbb rax, rdx
	mov QWORD PTR [rsp+24], rax
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+8]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+144], rax
	mov rax, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+16]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+136], rax
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+24]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+128], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 161
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 1
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 161
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 8
	mov QWORD PTR [rsp+176], rax
20:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_secp256k1_sign}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 21f
	xor edx, edx
	jmp 22f
21:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 33
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 97
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov edx, 1
	test rdx, rdx
22:
	jne 20b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	ret
	.p2align 6

vg_ecdsa_secp256k1_sha256_sign_shani:
	push rdi
	push rsi
	push rdx
	push rcx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rsp+64], rax
	movabs rdx, -4624529908474429119
	sub rax, rdx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rsp+72], rax
	movabs rdx, -4994812053365940165
	sbb rax, rdx
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rsp+80], rax
	movabs rdx, -2
	sbb rax, rdx
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rsp+88], rax
	movabs rdx, -1
	sbb rax, rdx
	mov QWORD PTR [rsp+24], rax
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+8]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+144], rax
	mov rax, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+16]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+136], rax
	mov rax, QWORD PTR [rsp+88]
	mov rcx, QWORD PTR [rsp+24]
	xor rax, rcx
	and rax, rdx
	xor rax, rcx
	bswap rax
	mov QWORD PTR [rsp+128], rax
	movabs rax, 72340172838076673
	xor ecx, ecx
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+56], rcx
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 161
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 1
	mov BYTE PTR [rdi+2288], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2289], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2297], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2305], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2313], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsp+152]
	mov QWORD PTR [rdi+2345], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 97
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 161
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 8
	mov QWORD PTR [rsp+176], rax
20:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi+3072]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rdi+3080]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rdi+3088]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rdi+3096]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rdi+3104]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rdi+3112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rdi+3120]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rdi+3128]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rdi+3136]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rdi+3144]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rdi+3152]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rdi+3232]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+3240]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rdi+3248]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rdi+3256]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rdi+3264]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+3272]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rdi+3280]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rdi+3288]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rdi+3296]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rdi+3304]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+3312]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rdi+3320]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rdi+3328]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rdi+3336]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rdi+3344]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rdi+3352]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rdi+3360]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rdi+3368]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rdi+3376]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rdi+3384]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rdi+3392]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rdi+3400]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rdi+3408]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rdi+3416]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rdi+3424]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+3432]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+3440]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rdi+3448]
	mov QWORD PTR [rdi+376], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_secp256k1_sign}
	mov rcx, QWORD PTR [rsp+176]
	sub rcx, 1
	mov QWORD PTR [rsp+176], rcx
	cmp eax, 1
	sbb rdx, rdx
	and rdx, rcx
	test rdx, rdx
	jne 21f
	xor edx, edx
	jmp 22f
21:
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov eax, 0
	mov BYTE PTR [rdi+2288], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 33
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 97
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3072], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+3080], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+3088], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+3096], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+3104], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+3112], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+3120], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+3128], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+3136], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+3144], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+3152], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+3160], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+3168], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+3176], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+3184], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+3192], rax
	mov rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+3200], rax
	mov rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3208], rax
	mov rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3216], rax
	mov rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3224], rax
	mov rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3240], rax
	mov rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3248], rax
	mov rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3256], rax
	mov rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3264], rax
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3272], rax
	mov rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+3280], rax
	mov rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+3288], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+3296], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+3304], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+3312], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+3320], rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+3328], rax
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+3336], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+3344], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+3352], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+3360], rax
	mov rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+3368], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+3376], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+3384], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+3392], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+3400], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+3408], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+3416], rax
	mov rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+3424], rax
	mov rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+3432], rax
	mov rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+3440], rax
	mov rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+3448], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 64
	mov rdx, rsp
	add rdx, 64
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 96
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov edx, 1
	test rdx, rdx
22:
	jne 20b
	xor ecx, ecx
	mov QWORD PTR [rsp], rcx
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], rcx
	mov QWORD PTR [rsp+32], rcx
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], rcx
	mov QWORD PTR [rsp+72], rcx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], rcx
	mov QWORD PTR [rsp+96], rcx
	mov QWORD PTR [rsp+104], rcx
	mov QWORD PTR [rsp+112], rcx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], rcx
	mov QWORD PTR [rsp+152], rcx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+168], rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	pop rcx
	ret
	.p2align 6
