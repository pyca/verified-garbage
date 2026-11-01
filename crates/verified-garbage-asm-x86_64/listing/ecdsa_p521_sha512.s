// The functions of `src/ecdsa_p521_sha512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sha512_sign:
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
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rsp+272], rax
	mov rsi, rsp
	add rsi, 216
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 9
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+266], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+258], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+250], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+242], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+234], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+226], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+218], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+216], dl
	mov rdx, rax
	mov BYTE PTR [rsp+217], dl
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
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 1
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
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
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+288], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+328], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp+336], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rsp+344], rax
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+352], rax
	mov rsi, rsp
	add rsi, 288
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 7
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+346], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+338], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+330], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+322], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+314], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+306], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+298], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+290], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+288], dl
	mov rdx, rax
	mov BYTE PTR [rsp+289], dl
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 288
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_p521_sign}
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
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 65
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 193
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
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
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
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

vg_ecdsa_p521_sha512_sign_adx:
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
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rsp+272], rax
	mov rsi, rsp
	add rsi, 216
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 9
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+266], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+258], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+250], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+242], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+234], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+226], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+218], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+216], dl
	mov rdx, rax
	mov BYTE PTR [rsp+217], dl
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
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 1
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
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
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+288], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+328], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp+336], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rsp+344], rax
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+352], rax
	mov rsi, rsp
	add rsi, 288
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 7
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+346], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+338], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+330], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+322], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+314], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+306], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+298], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+290], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+288], dl
	mov rdx, rax
	mov BYTE PTR [rsp+289], dl
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 288
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_p521_sign_adx}
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
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 65
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 193
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch}
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
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
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

vg_ecdsa_p521_sha512_sign_avx2:
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
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rsp+272], rax
	mov rsi, rsp
	add rsi, 216
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 9
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+266], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+258], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+250], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+242], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+234], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+226], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+218], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+216], dl
	mov rdx, rax
	mov BYTE PTR [rsp+217], dl
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
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 1
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
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
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+288], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+328], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp+336], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rsp+344], rax
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+352], rax
	mov rsi, rsp
	add rsi, 288
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 7
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+346], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+338], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+330], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+322], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+314], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+306], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+298], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+290], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+288], dl
	mov rdx, rax
	mov BYTE PTR [rsp+289], dl
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 288
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_p521_sign}
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
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 65
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 193
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
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
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
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

vg_ecdsa_p521_sha512_sign_avx2_adx:
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
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rsp+272], rax
	mov rsi, rsp
	add rsi, 216
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 9
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+266], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+258], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+250], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+242], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+234], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+226], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+218], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+216], dl
	mov rdx, rax
	mov BYTE PTR [rsp+217], dl
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
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 1
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
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
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+288], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+328], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp+336], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rsp+344], rax
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+352], rax
	mov rsi, rsp
	add rsi, 288
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 7
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+346], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+338], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+330], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+322], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+314], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+306], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+298], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+290], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+288], dl
	mov rdx, rax
	mov BYTE PTR [rsp+289], dl
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 288
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_p521_sign_adx}
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
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 65
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 193
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_avx2}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_avx2}
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
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
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

vg_ecdsa_p521_sha512_sign_shani:
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
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rsp+272], rax
	mov rsi, rsp
	add rsi, 216
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 9
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+266], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+258], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+250], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+242], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+234], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+226], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+218], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+216], dl
	mov rdx, rax
	mov BYTE PTR [rsp+217], dl
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
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 1
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
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
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+288], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+328], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp+336], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rsp+344], rax
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+352], rax
	mov rsi, rsp
	add rsi, 288
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 7
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+346], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+338], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+330], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+322], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+314], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+306], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+298], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+290], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+288], dl
	mov rdx, rax
	mov BYTE PTR [rsp+289], dl
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 288
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_p521_sign}
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
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 65
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 193
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
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
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
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

vg_ecdsa_p521_sha512_sign_shani_adx:
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
	mov rdi, QWORD PTR [rsp+184]
	xor eax, eax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rsp+264], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rsp+272], rax
	mov rsi, rsp
	add rsi, 216
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 9
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 511
	ror rdx, 9
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 9
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+274], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+266], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+258], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+250], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+242], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+234], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+226], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+218], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+216], dl
	mov rdx, rax
	mov BYTE PTR [rsp+217], dl
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
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+192]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 1
	mov BYTE PTR [rdi+2320], al
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi+2321], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+2329], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+2337], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+2345], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+2353], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+2361], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+2369], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+2377], rax
	mov rax, QWORD PTR [rsi+58]
	mov QWORD PTR [rdi+2379], rax
	xor eax, eax
	mov QWORD PTR [rdi+2387], rax
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdi+2389], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdi+2397], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdi+2405], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+2413], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdi+2421], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi+2429], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdi+2437], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdi+2445], rax
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
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 197
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 325
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+288], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+328], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp+336], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rsp+344], rax
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp+352], rax
	mov rsi, rsp
	add rsi, 288
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2624], rax
	mov rax, QWORD PTR [rdi+2560]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2568]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2560], rax
	mov rax, QWORD PTR [rdi+2568]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2576]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2568], rax
	mov rax, QWORD PTR [rdi+2576]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2584]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2576], rax
	mov rax, QWORD PTR [rdi+2584]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2592]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2584], rax
	mov rax, QWORD PTR [rdi+2592]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2600]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2592], rax
	mov rax, QWORD PTR [rdi+2600]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2608]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2600], rax
	mov rax, QWORD PTR [rdi+2608]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2616]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2608], rax
	mov rax, QWORD PTR [rdi+2616]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2624]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2616], rax
	mov rax, QWORD PTR [rdi+2624]
	shr rax, 7
	mov QWORD PTR [rdi+2624], rax
	movabs rcx, -1
	mov rax, QWORD PTR [rdi+2560]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+346], rax
	mov rax, QWORD PTR [rdi+2568]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+338], rax
	mov rax, QWORD PTR [rdi+2576]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+330], rax
	mov rax, QWORD PTR [rdi+2584]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+322], rax
	mov rax, QWORD PTR [rdi+2592]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+314], rax
	mov rax, QWORD PTR [rdi+2600]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+306], rax
	mov rax, QWORD PTR [rdi+2608]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+298], rax
	mov rax, QWORD PTR [rdi+2616]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsp+290], rax
	mov rax, QWORD PTR [rdi+2624]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsp+288], dl
	mov rdx, rax
	mov BYTE PTR [rsp+289], dl
	mov rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+200]
	mov rdx, rsp
	add rdx, 216
	mov rcx, rsp
	add rcx, 288
	mov r8, QWORD PTR [rsp+184]
	call {vg_ecdsa_p521_sign_adx}
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
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rdi+2288], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rsp+120]
	mov QWORD PTR [rdi+2312], rax
	mov eax, 0
	mov BYTE PTR [rdi+2320], al
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov esi, 128
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2256
	mov ecx, 65
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 193
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov rdx, rsp
	add rdx, 0
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_init_scratch_shani}
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
	mov esi, 128
	mov rdx, rsp
	add rdx, 64
	mov ecx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 192
	mov edx, 192
	mov rcx, rsp
	add rcx, 64
	mov r8, QWORD PTR [rsp+184]
	add r8, 384
	call {vg_hmac_sha512_finalize_scratch_shani}
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
	mov QWORD PTR [rsp+216], rcx
	mov QWORD PTR [rsp+224], rcx
	mov QWORD PTR [rsp+232], rcx
	mov QWORD PTR [rsp+240], rcx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rcx
	mov QWORD PTR [rsp+264], rcx
	mov QWORD PTR [rsp+272], rcx
	mov QWORD PTR [rsp+280], rcx
	mov QWORD PTR [rsp+288], rcx
	mov QWORD PTR [rsp+296], rcx
	mov QWORD PTR [rsp+304], rcx
	mov QWORD PTR [rsp+312], rcx
	mov QWORD PTR [rsp+320], rcx
	mov QWORD PTR [rsp+328], rcx
	mov QWORD PTR [rsp+336], rcx
	mov QWORD PTR [rsp+344], rcx
	mov QWORD PTR [rsp+352], rcx
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
