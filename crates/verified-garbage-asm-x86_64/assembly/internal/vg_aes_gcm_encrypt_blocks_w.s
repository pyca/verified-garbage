// The functions of `src/internal/vg_aes_gcm_encrypt_blocks_w.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_encrypt_blocks_w:
	mov r11, QWORD PTR [rsp+8]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], rdx
	mov QWORD PTR [r11+24], rcx
	mov QWORD PTR [r11+32], r8
	mov QWORD PTR [r11+40], r9
	mov r11, QWORD PTR [rsp+8]
	mov r8, QWORD PTR [r11+40]
	test r8, r8
	je 20f
	mov r11, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+32]
	mov r8, QWORD PTR [r11+40]
	mov r9, r11
	add r9, 64
	call {vg_aes_ctr32}
	mov r11, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [r11]
	add rdi, 240
	mov rsi, QWORD PTR [r11+24]
	mov rdx, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+40]
	mov r8, r11
	add r8, 64
	call {vg_ghash}
	jmp 21f
20:
21:
	mov r11, QWORD PTR [rsp+8]
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r11+1528], xmm0
	movdqu XMMWORD PTR [r11+1520], xmm0
	movdqu XMMWORD PTR [r11+1504], xmm0
	movdqu XMMWORD PTR [r11+1488], xmm0
	movdqu XMMWORD PTR [r11+1472], xmm0
	movdqu XMMWORD PTR [r11+1456], xmm0
	movdqu XMMWORD PTR [r11+1440], xmm0
	movdqu XMMWORD PTR [r11+1424], xmm0
	movdqu XMMWORD PTR [r11+1408], xmm0
	movdqu XMMWORD PTR [r11+1392], xmm0
	movdqu XMMWORD PTR [r11+1376], xmm0
	movdqu XMMWORD PTR [r11+1360], xmm0
	movdqu XMMWORD PTR [r11+1344], xmm0
	movdqu XMMWORD PTR [r11+1328], xmm0
	movdqu XMMWORD PTR [r11+1312], xmm0
	movdqu XMMWORD PTR [r11+1296], xmm0
	movdqu XMMWORD PTR [r11+1280], xmm0
	movdqu XMMWORD PTR [r11+1264], xmm0
	movdqu XMMWORD PTR [r11+1248], xmm0
	movdqu XMMWORD PTR [r11+1232], xmm0
	movdqu XMMWORD PTR [r11+1216], xmm0
	movdqu XMMWORD PTR [r11+1200], xmm0
	movdqu XMMWORD PTR [r11+1184], xmm0
	movdqu XMMWORD PTR [r11+1168], xmm0
	movdqu XMMWORD PTR [r11+1152], xmm0
	movdqu XMMWORD PTR [r11+1136], xmm0
	movdqu XMMWORD PTR [r11+1120], xmm0
	movdqu XMMWORD PTR [r11+1104], xmm0
	movdqu XMMWORD PTR [r11+1088], xmm0
	movdqu XMMWORD PTR [r11+1072], xmm0
	movdqu XMMWORD PTR [r11+1056], xmm0
	movdqu XMMWORD PTR [r11+1040], xmm0
	movdqu XMMWORD PTR [r11+1024], xmm0
	movdqu XMMWORD PTR [r11+1008], xmm0
	movdqu XMMWORD PTR [r11+992], xmm0
	movdqu XMMWORD PTR [r11+976], xmm0
	movdqu XMMWORD PTR [r11+960], xmm0
	movdqu XMMWORD PTR [r11+944], xmm0
	movdqu XMMWORD PTR [r11+928], xmm0
	movdqu XMMWORD PTR [r11+912], xmm0
	movdqu XMMWORD PTR [r11+896], xmm0
	movdqu XMMWORD PTR [r11+880], xmm0
	movdqu XMMWORD PTR [r11+864], xmm0
	movdqu XMMWORD PTR [r11+848], xmm0
	movdqu XMMWORD PTR [r11+832], xmm0
	movdqu XMMWORD PTR [r11+816], xmm0
	movdqu XMMWORD PTR [r11+800], xmm0
	movdqu XMMWORD PTR [r11+784], xmm0
	movdqu XMMWORD PTR [r11+768], xmm0
	movdqu XMMWORD PTR [r11+752], xmm0
	movdqu XMMWORD PTR [r11+736], xmm0
	movdqu XMMWORD PTR [r11+720], xmm0
	movdqu XMMWORD PTR [r11+704], xmm0
	movdqu XMMWORD PTR [r11+688], xmm0
	movdqu XMMWORD PTR [r11+672], xmm0
	movdqu XMMWORD PTR [r11+656], xmm0
	movdqu XMMWORD PTR [r11+640], xmm0
	movdqu XMMWORD PTR [r11+624], xmm0
	movdqu XMMWORD PTR [r11+608], xmm0
	movdqu XMMWORD PTR [r11+592], xmm0
	movdqu XMMWORD PTR [r11+576], xmm0
	movdqu XMMWORD PTR [r11+560], xmm0
	movdqu XMMWORD PTR [r11+544], xmm0
	movdqu XMMWORD PTR [r11+528], xmm0
	movdqu XMMWORD PTR [r11+512], xmm0
	movdqu XMMWORD PTR [r11+496], xmm0
	movdqu XMMWORD PTR [r11+480], xmm0
	movdqu XMMWORD PTR [r11+464], xmm0
	movdqu XMMWORD PTR [r11+448], xmm0
	movdqu XMMWORD PTR [r11+432], xmm0
	movdqu XMMWORD PTR [r11+416], xmm0
	movdqu XMMWORD PTR [r11+400], xmm0
	movdqu XMMWORD PTR [r11+384], xmm0
	movdqu XMMWORD PTR [r11+368], xmm0
	movdqu XMMWORD PTR [r11+352], xmm0
	movdqu XMMWORD PTR [r11+336], xmm0
	movdqu XMMWORD PTR [r11+320], xmm0
	movdqu XMMWORD PTR [r11+304], xmm0
	movdqu XMMWORD PTR [r11+288], xmm0
	movdqu XMMWORD PTR [r11+272], xmm0
	movdqu XMMWORD PTR [r11+256], xmm0
	movdqu XMMWORD PTR [r11+240], xmm0
	movdqu XMMWORD PTR [r11+224], xmm0
	movdqu XMMWORD PTR [r11+208], xmm0
	movdqu XMMWORD PTR [r11+192], xmm0
	movdqu XMMWORD PTR [r11+176], xmm0
	movdqu XMMWORD PTR [r11+160], xmm0
	movdqu XMMWORD PTR [r11+144], xmm0
	movdqu XMMWORD PTR [r11+128], xmm0
	movdqu XMMWORD PTR [r11+112], xmm0
	movdqu XMMWORD PTR [r11+96], xmm0
	movdqu XMMWORD PTR [r11+80], xmm0
	movdqu XMMWORD PTR [r11+64], xmm0
	ret
	.p2align 6
