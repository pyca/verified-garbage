// The functions of `src/internal/vg_ecdsa_p256_verify_tail_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_verify_tail_adx:
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	movabs rax, 3
	mov QWORD PTR [rdi+1152], rax
	movabs rax, -17179869185
	mov QWORD PTR [rdi+1160], rax
	movabs rax, -2
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 21474836477
	mov QWORD PTR [rdi+1176], rax
	movabs rax, -7290930562918386328
	mov QWORD PTR [rdi+992], rax
	movabs rax, -8525026828342093519
	mov QWORD PTR [rdi+1000], rax
	movabs rax, -7205364892169234761
	mov QWORD PTR [rdi+1008], rax
	movabs rax, -7465688212940058645
	mov QWORD PTR [rdi+1016], rax
	movabs rax, 884452912994769582
	mov QWORD PTR [rdi+96], rax
	movabs rax, 4834901530490986875
	mov QWORD PTR [rdi+104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+120], rax
	mov rdx, QWORD PTR [rdi+1056]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1152]
	mulx r10, rax, QWORD PTR [rdi+1160]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1168]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1176]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1064]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1072]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1080]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1176]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov rdx, QWORD PTR [rdi+1152]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1160]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1168]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1176]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+1184]
	sbb r9, QWORD PTR [rdi+1192]
	sbb r10, QWORD PTR [rdi+1200]
	sbb r11, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1344], r8
	mov QWORD PTR [rdi+1352], r9
	mov QWORD PTR [rdi+1360], r10
	mov QWORD PTR [rdi+1368], r11
	mov r8, QWORD PTR [rdi+1152]
	mov r9, QWORD PTR [rdi+1160]
	mov r10, QWORD PTR [rdi+1168]
	mov r11, QWORD PTR [rdi+1176]
	mov r12d, 0
	add r8, QWORD PTR [rdi+992]
	adc r9, QWORD PTR [rdi+1000]
	adc r10, QWORD PTR [rdi+1008]
	adc r11, QWORD PTR [rdi+1016]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+1152], r8
	mov QWORD PTR [rdi+1160], r9
	mov QWORD PTR [rdi+1168], r10
	mov QWORD PTR [rdi+1176], r11
	mov rdx, QWORD PTR [rdi+1152]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1160]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1168]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1176]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+1184]
	sbb r9, QWORD PTR [rdi+1192]
	sbb r10, QWORD PTR [rdi+1200]
	sbb r11, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov rdx, QWORD PTR [rdi+1344]
	or rdx, QWORD PTR [rdi+1352]
	or rdx, QWORD PTR [rdi+1360]
	or rdx, QWORD PTR [rdi+1368]
	cmp rdx, 1
	sbb rdx, rdx
	mov rbp, rdx
	mov rdx, QWORD PTR [rdi+1056]
	sub rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1064]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1072]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1080]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov r12, rax
	mov rdx, QWORD PTR [rdi+1280]
	or rdx, QWORD PTR [rdi+1288]
	or rdx, QWORD PTR [rdi+1296]
	or rdx, QWORD PTR [rdi+1304]
	cmp rdx, 1
	sbb rdx, rdx
	and rdx, r12
	or rdx, rbp
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+576]
	or rdx, QWORD PTR [rdi+584]
	or rdx, QWORD PTR [rdi+592]
	or rdx, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1472]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
