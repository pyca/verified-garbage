// The functions of `src/camellia.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_expand_key:
	lea rsp, [rsp-3216]
	mov rcx, rsp
	add rcx, 8
	mov r9, rcx
	mov QWORD PTR [r9+2968], rbx
	mov QWORD PTR [r9+2976], rbp
	mov QWORD PTR [r9+2984], r12
	mov QWORD PTR [r9+2992], r13
	mov QWORD PTR [r9+3000], r14
	mov QWORD PTR [r9+3008], r15
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+384], r14
	movabs r14, -71777214294589696
	mov QWORD PTR [r9+392], r14
	movabs r14, 72056494526300160
	mov QWORD PTR [r9+400], r14
	movabs r14, 16776960
	mov QWORD PTR [r9+408], r14
	movabs r14, 1099494850560
	mov QWORD PTR [r9+416], r14
	mov QWORD PTR [r9+2952], rsi
	mov rsi, r9
	add rsi, 768
	movabs rax, -281474976645376
	mov QWORD PTR [rsi], rax
	movabs rax, -280379743273216
	mov QWORD PTR [rsi+8], rax
	movabs rax, 71777218572779520
	mov QWORD PTR [rsi+16], rax
	movabs rax, -281470681743616
	mov QWORD PTR [rsi+24], rax
	movabs rax, 72056494543077120
	mov QWORD PTR [rsi+32], rax
	movabs rax, 71777214277943295
	mov QWORD PTR [rsi+40], rax
	movabs rax, 71777218556067840
	mov QWORD PTR [rsi+48], rax
	movabs rax, -71777214277943041
	mov QWORD PTR [rsi+56], rax
	add rsi, 64
	movabs rax, 280375465082880
	mov QWORD PTR [rsi], rax
	movabs rax, -71777214277943041
	mov QWORD PTR [rsi+8], rax
	movabs rax, 65535
	mov QWORD PTR [rsi+16], rax
	movabs rax, 71777218572844800
	mov QWORD PTR [rsi+24], rax
	movabs rax, -1099494915841
	mov QWORD PTR [rsi+32], rax
	movabs rax, -71776119061282561
	mov QWORD PTR [rsi+40], rax
	movabs rax, 72057589759737600
	mov QWORD PTR [rsi+48], rax
	movabs rax, -72056494543077121
	mov QWORD PTR [rsi+56], rax
	add rsi, 64
	movabs rax, 71777218572844800
	mov QWORD PTR [rsi], rax
	movabs rax, -65281
	mov QWORD PTR [rsi+8], rax
	movabs rax, -280375465148161
	mov QWORD PTR [rsi+16], rax
	movabs rax, -281470681743616
	mov QWORD PTR [rsi+24], rax
	movabs rax, -72056498821267456
	mov QWORD PTR [rsi+32], rax
	movabs rax, -280379743273216
	mov QWORD PTR [rsi+40], rax
	movabs rax, 4294967295
	mov QWORD PTR [rsi+48], rax
	movabs rax, -71777218556067841
	mov QWORD PTR [rsi+56], rax
	add rsi, 64
	movabs rax, 72057594037927680
	mov QWORD PTR [rsi], rax
	movabs rax, 281474976645120
	mov QWORD PTR [rsi+8], rax
	movabs rax, -1099494915841
	mov QWORD PTR [rsi+16], rax
	movabs rax, -71777218556133376
	mov QWORD PTR [rsi+24], rax
	movabs rax, -72056494526300161
	mov QWORD PTR [rsi+32], rax
	movabs rax, 72056494543077120
	mov QWORD PTR [rsi+40], rax
	movabs rax, 281474976710655
	mov QWORD PTR [rsi+48], rax
	movabs rax, 71776123356184320
	mov QWORD PTR [rsi+56], rax
	add rsi, 64
	movabs rax, -71776123339472896
	mov QWORD PTR [rsi], rax
	movabs rax, 71777214277943040
	mov QWORD PTR [rsi+8], rax
	movabs rax, -71776123339407616
	mov QWORD PTR [rsi+16], rax
	movabs rax, -1095233372416
	mov QWORD PTR [rsi+24], rax
	movabs rax, -281474976645121
	mov QWORD PTR [rsi+32], rax
	movabs rax, 72057594037862400
	mov QWORD PTR [rsi+40], rax
	movabs rax, 71776123356184320
	mov QWORD PTR [rsi+48], rax
	movabs rax, 71776119077994240
	mov QWORD PTR [rsi+56], rax
	add rsi, 64
	movabs rax, -71777218572779776
	mov QWORD PTR [rsi], rax
	movabs rax, 71776123356184320
	mov QWORD PTR [rsi+8], rax
	movabs rax, -72057589743026176
	mov QWORD PTR [rsi+16], rax
	movabs rax, -72056498821267456
	mov QWORD PTR [rsi+24], rax
	movabs rax, -72057594021150721
	mov QWORD PTR [rsi+32], rax
	movabs rax, -72057589759672321
	mov QWORD PTR [rsi+40], rax
	movabs rax, -1095216726016
	mov QWORD PTR [rsi+48], rax
	movabs rax, -16711681
	mov QWORD PTR [rsi+56], rax
	add rsi, 64
	mov rsi, QWORD PTR [r9+2952]
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+3016], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+3024], rax
	cmp rsi, 16
	je 20f
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+3032], rax
	cmp rsi, 24
	je 22f
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+3040], rax
	jmp 23f
22:
	xor rax, -1
	mov QWORD PTR [r9+3040], rax
23:
	jmp 21f
20:
	mov eax, 0
	mov QWORD PTR [r9+3032], rax
	mov QWORD PTR [r9+3040], rax
21:
	mov rsi, r9
	add rsi, 768
	mov rax, QWORD PTR [r9+3016]
	mov QWORD PTR [r9+3048], rax
	mov rax, QWORD PTR [r9+3024]
	mov QWORD PTR [r9+3056], rax
	mov rax, QWORD PTR [r9+3032]
	xor rax, QWORD PTR [r9+3048]
	mov QWORD PTR [r9+3048], rax
	mov rax, QWORD PTR [r9+3040]
	xor rax, QWORD PTR [r9+3056]
	mov QWORD PTR [r9+3056], rax
	movabs r8, 3
	mov rdi, r9
	add rdi, 3048
24:
	mov rax, QWORD PTR [rdi+8]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [r9+576], rax
	mov QWORD PTR [r9+584], rbx
	mov QWORD PTR [r9+592], rcx
	mov QWORD PTR [r9+600], rbp
	mov QWORD PTR [r9+608], r10
	mov QWORD PTR [r9+616], r11
	mov QWORD PTR [r9+624], r12
	mov QWORD PTR [r9+632], r13
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [r9+512], rax
	mov QWORD PTR [r9+520], rbx
	mov QWORD PTR [r9+528], rcx
	mov QWORD PTR [r9+536], rbp
	mov QWORD PTR [r9+544], r10
	mov QWORD PTR [r9+552], r11
	mov QWORD PTR [r9+560], r12
	mov QWORD PTR [r9+568], r13
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r13
	xor r14, rbx
	mov r15, r11
	xor r15, rbp
	mov QWORD PTR [r9+8], r11
	mov r11, rcx
	xor r11, r14
	mov QWORD PTR [r9+16], r14
	mov r14, r12
	xor r14, rax
	mov QWORD PTR [r9+24], rbp
	mov rbp, rax
	xor rbp, r15
	mov QWORD PTR [r9+32], rbp
	mov rbp, r10
	xor rbp, rbx
	mov QWORD PTR [r9+40], rbp
	mov rbp, r10
	xor rbp, r11
	mov QWORD PTR [r9+48], rbp
	mov rbp, r12
	xor rbp, r15
	mov QWORD PTR [r9+56], r15
	mov r15, rcx
	xor r15, r14
	mov QWORD PTR [r9+64], r15
	mov r15, r11
	xor r15, r14
	mov QWORD PTR [r9+72], r15
	mov r15, r13
	xor r15, r12
	mov QWORD PTR [r9+80], rbp
	mov rbp, r13
	xor rbp, r14
	xor rbp, QWORD PTR [r9]
	mov QWORD PTR [r9+88], rbp
	mov rbp, r12
	xor rbp, QWORD PTR [r9+24]
	mov QWORD PTR [r9+96], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, rbx
	mov QWORD PTR [r9+104], r12
	mov r12, QWORD PTR [r9+8]
	xor r12, rax
	mov QWORD PTR [r9+112], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, r11
	xor r14, r10
	xor r10, r15
	xor rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9]
	mov r15, rcx
	xor r15, QWORD PTR [r9+32]
	xor rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+80]
	xor r14, QWORD PTR [r9]
	mov QWORD PTR [r9+8], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov QWORD PTR [r9+120], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+40]
	mov QWORD PTR [r9+16], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+48]
	mov QWORD PTR [r9+128], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+72]
	mov QWORD PTR [r9+56], r14
	mov r14, r11
	xor r14, QWORD PTR [r9+32]
	xor r14, QWORD PTR [r9]
	xor r11, rbp
	xor r11, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+40]
	xor rbp, QWORD PTR [r9]
	xor r12, QWORD PTR [r9+48]
	xor r12, QWORD PTR [r9]
	mov QWORD PTR [r9+40], r11
	mov r11, QWORD PTR [r9+64]
	xor r11, QWORD PTR [r9+112]
	xor r11, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r9+96]
	xor rax, QWORD PTR [r9+104]
	xor rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9]
	mov QWORD PTR [r9+96], rbx
	mov rbx, rcx
	and rbx, r10
	mov QWORD PTR [r9+104], rcx
	mov rcx, rax
	and rcx, r11
	xor rcx, rbx
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [r9+48]
	and rax, r12
	xor rax, rbx
	mov rbx, r15
	and rbx, r14
	mov QWORD PTR [r9+32], r15
	mov r15, QWORD PTR [r9+16]
	and r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+136], r13
	mov r13, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+80]
	xor r13, rbx
	mov rbx, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+128]
	mov QWORD PTR [r9+144], r14
	mov r14, rbp
	and r14, QWORD PTR [r9+64]
	xor r14, rbx
	mov QWORD PTR [r9+152], rbp
	mov rbp, QWORD PTR [r9+8]
	and rbp, QWORD PTR [r9+88]
	xor rbp, rbx
	xor rcx, r14
	xor rax, rbp
	xor r15, r14
	xor r13, rbp
	xor rcx, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+120]
	xor r15, QWORD PTR [r9+96]
	xor r13, QWORD PTR [r9+40]
	mov rbp, rcx
	xor rbp, rax
	and rcx, r15
	mov r14, r13
	xor r14, rcx
	mov rbx, rbp
	and rbx, r14
	xor rbx, rax
	mov QWORD PTR [r9+40], r12
	mov r12, r15
	xor r12, r13
	xor rax, rcx
	and rax, r12
	xor rax, r13
	xor r15, rax
	mov r12, r14
	xor r12, rax
	and r13, r12
	xor r15, r13
	xor r14, r13
	and r14, rbx
	xor rbp, r14
	mov r14, rbp
	xor r14, r15
	mov r13, rbx
	xor r13, rax
	mov r12, rbx
	xor r12, rbp
	mov rcx, rax
	xor rcx, r15
	mov QWORD PTR [r9+96], rbx
	mov rbx, r13
	xor rbx, r14
	and r10, rcx
	and r11, r15
	mov QWORD PTR [r9+120], r10
	mov r10, rax
	and r10, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r10
	mov r10, r12
	and r10, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], r10
	mov r10, rbp
	and r10, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], r10
	mov r10, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, r13
	and r10, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r10
	mov r10, rbx
	and r10, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r10
	mov r10, r14
	and r10, QWORD PTR [r9+88]
	and rcx, QWORD PTR [r9+104]
	and r15, QWORD PTR [r9+112]
	and rax, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	and rbp, QWORD PTR [r9+16]
	mov QWORD PTR [r9+16], rbp
	mov rbp, QWORD PTR [r9+96]
	and rbp, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+152]
	and r14, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], r15
	mov r15, r11
	xor r15, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r11
	mov r11, QWORD PTR [r9+144]
	xor r11, QWORD PTR [r9+80]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+128]
	xor rcx, r10
	mov QWORD PTR [r9+152], r10
	mov r10, QWORD PTR [r9+120]
	xor r10, rbx
	xor rax, r15
	mov QWORD PTR [r9+24], r15
	mov r15, r12
	xor r15, r11
	mov QWORD PTR [r9+72], r11
	mov r11, r13
	xor r11, rcx
	xor rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+96], rbp
	mov rbp, QWORD PTR [r9+128]
	xor rbp, r14
	mov QWORD PTR [r9+128], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+144]
	mov QWORD PTR [r9+152], rcx
	mov rcx, QWORD PTR [r9+144]
	xor rcx, QWORD PTR [r9+8]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+16]
	xor rcx, r15
	xor rbx, r11
	mov QWORD PTR [r9+16], rbx
	mov rbx, r10
	xor rbx, rax
	mov QWORD PTR [r9+32], rbx
	mov rbx, QWORD PTR [r9+120]
	xor rbx, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], rcx
	mov rcx, QWORD PTR [r9+64]
	xor rcx, QWORD PTR [r9+136]
	xor r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, QWORD PTR [r9+8]
	xor r10, rbp
	xor r12, rax
	xor r13, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+152]
	mov rax, QWORD PTR [r9+72]
	xor rax, QWORD PTR [r9+144]
	xor rbx, QWORD PTR [r9+128]
	xor r15, QWORD PTR [r9+96]
	xor r11, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rbx
	mov rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9+152]
	xor rbp, r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+16]
	mov QWORD PTR [r9+152], r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+32]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9]
	xor r10, QWORD PTR [r9+32]
	xor r10, QWORD PTR [r9]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rbx
	xor r12, QWORD PTR [r9]
	xor r14, r13
	xor r14, QWORD PTR [r9]
	xor r15, rbp
	xor r11, rcx
	xor r11, QWORD PTR [r9]
	mov r13, r15
	mov QWORD PTR [r9+80], r12
	mov r12, r11
	mov r11, rax
	mov QWORD PTR [r9+32], r10
	mov r10, QWORD PTR [r9+144]
	mov rbp, QWORD PTR [r9+80]
	mov rcx, QWORD PTR [r9+32]
	mov rbx, r14
	mov rax, QWORD PTR [r9+152]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+408]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+408]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+408]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+408]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+408]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+408]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+408]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+408]
	xor rax, r14
	mov r15, rax
	mov r14, rax
	xor r14, rbx
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov r14, rbx
	xor r14, rcx
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	mov r14, rcx
	xor r14, rbp
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	mov r14, rbp
	xor r14, r10
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	mov r14, r10
	xor r14, r11
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	mov r14, r11
	xor r14, r12
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	mov r14, r12
	xor r14, r13
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	mov r14, r13
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	xor r13, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	xor rax, QWORD PTR [r9+576]
	mov QWORD PTR [r9+576], rax
	xor rbx, QWORD PTR [r9+584]
	mov QWORD PTR [r9+584], rbx
	xor rcx, QWORD PTR [r9+592]
	mov QWORD PTR [r9+592], rcx
	xor rbp, QWORD PTR [r9+600]
	mov QWORD PTR [r9+600], rbp
	xor r10, QWORD PTR [r9+608]
	mov QWORD PTR [r9+608], r10
	xor r11, QWORD PTR [r9+616]
	mov QWORD PTR [r9+616], r11
	xor r12, QWORD PTR [r9+624]
	mov QWORD PTR [r9+624], r12
	xor r13, QWORD PTR [r9+632]
	mov QWORD PTR [r9+632], r13
	xor rax, QWORD PTR [rsi+64]
	xor rbx, QWORD PTR [rsi+72]
	xor rcx, QWORD PTR [rsi+80]
	xor rbp, QWORD PTR [rsi+88]
	xor r10, QWORD PTR [rsi+96]
	xor r11, QWORD PTR [rsi+104]
	xor r12, QWORD PTR [rsi+112]
	xor r13, QWORD PTR [rsi+120]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r13
	xor r14, rbx
	mov r15, r11
	xor r15, rbp
	mov QWORD PTR [r9+8], r11
	mov r11, rcx
	xor r11, r14
	mov QWORD PTR [r9+16], r14
	mov r14, r12
	xor r14, rax
	mov QWORD PTR [r9+24], rbp
	mov rbp, rax
	xor rbp, r15
	mov QWORD PTR [r9+32], rbp
	mov rbp, r10
	xor rbp, rbx
	mov QWORD PTR [r9+40], rbp
	mov rbp, r10
	xor rbp, r11
	mov QWORD PTR [r9+48], rbp
	mov rbp, r12
	xor rbp, r15
	mov QWORD PTR [r9+56], r15
	mov r15, rcx
	xor r15, r14
	mov QWORD PTR [r9+64], r15
	mov r15, r11
	xor r15, r14
	mov QWORD PTR [r9+72], r15
	mov r15, r13
	xor r15, r12
	mov QWORD PTR [r9+80], rbp
	mov rbp, r13
	xor rbp, r14
	xor rbp, QWORD PTR [r9]
	mov QWORD PTR [r9+88], rbp
	mov rbp, r12
	xor rbp, QWORD PTR [r9+24]
	mov QWORD PTR [r9+96], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, rbx
	mov QWORD PTR [r9+104], r12
	mov r12, QWORD PTR [r9+8]
	xor r12, rax
	mov QWORD PTR [r9+112], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, r11
	xor r14, r10
	xor r10, r15
	xor rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9]
	mov r15, rcx
	xor r15, QWORD PTR [r9+32]
	xor rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+80]
	xor r14, QWORD PTR [r9]
	mov QWORD PTR [r9+8], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov QWORD PTR [r9+120], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+40]
	mov QWORD PTR [r9+16], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+48]
	mov QWORD PTR [r9+128], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+72]
	mov QWORD PTR [r9+56], r14
	mov r14, r11
	xor r14, QWORD PTR [r9+32]
	xor r14, QWORD PTR [r9]
	xor r11, rbp
	xor r11, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+40]
	xor rbp, QWORD PTR [r9]
	xor r12, QWORD PTR [r9+48]
	xor r12, QWORD PTR [r9]
	mov QWORD PTR [r9+40], r11
	mov r11, QWORD PTR [r9+64]
	xor r11, QWORD PTR [r9+112]
	xor r11, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r9+96]
	xor rax, QWORD PTR [r9+104]
	xor rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9]
	mov QWORD PTR [r9+96], rbx
	mov rbx, rcx
	and rbx, r10
	mov QWORD PTR [r9+104], rcx
	mov rcx, rax
	and rcx, r11
	xor rcx, rbx
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [r9+48]
	and rax, r12
	xor rax, rbx
	mov rbx, r15
	and rbx, r14
	mov QWORD PTR [r9+32], r15
	mov r15, QWORD PTR [r9+16]
	and r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+136], r13
	mov r13, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+80]
	xor r13, rbx
	mov rbx, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+128]
	mov QWORD PTR [r9+144], r14
	mov r14, rbp
	and r14, QWORD PTR [r9+64]
	xor r14, rbx
	mov QWORD PTR [r9+152], rbp
	mov rbp, QWORD PTR [r9+8]
	and rbp, QWORD PTR [r9+88]
	xor rbp, rbx
	xor rcx, r14
	xor rax, rbp
	xor r15, r14
	xor r13, rbp
	xor rcx, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+120]
	xor r15, QWORD PTR [r9+96]
	xor r13, QWORD PTR [r9+40]
	mov rbp, rcx
	xor rbp, rax
	and rcx, r15
	mov r14, r13
	xor r14, rcx
	mov rbx, rbp
	and rbx, r14
	xor rbx, rax
	mov QWORD PTR [r9+40], r12
	mov r12, r15
	xor r12, r13
	xor rax, rcx
	and rax, r12
	xor rax, r13
	xor r15, rax
	mov r12, r14
	xor r12, rax
	and r13, r12
	xor r15, r13
	xor r14, r13
	and r14, rbx
	xor rbp, r14
	mov r14, rbp
	xor r14, r15
	mov r13, rbx
	xor r13, rax
	mov r12, rbx
	xor r12, rbp
	mov rcx, rax
	xor rcx, r15
	mov QWORD PTR [r9+96], rbx
	mov rbx, r13
	xor rbx, r14
	and r10, rcx
	and r11, r15
	mov QWORD PTR [r9+120], r10
	mov r10, rax
	and r10, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r10
	mov r10, r12
	and r10, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], r10
	mov r10, rbp
	and r10, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], r10
	mov r10, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, r13
	and r10, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r10
	mov r10, rbx
	and r10, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r10
	mov r10, r14
	and r10, QWORD PTR [r9+88]
	and rcx, QWORD PTR [r9+104]
	and r15, QWORD PTR [r9+112]
	and rax, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	and rbp, QWORD PTR [r9+16]
	mov QWORD PTR [r9+16], rbp
	mov rbp, QWORD PTR [r9+96]
	and rbp, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+152]
	and r14, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], r15
	mov r15, r11
	xor r15, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r11
	mov r11, QWORD PTR [r9+144]
	xor r11, QWORD PTR [r9+80]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+128]
	xor rcx, r10
	mov QWORD PTR [r9+152], r10
	mov r10, QWORD PTR [r9+120]
	xor r10, rbx
	xor rax, r15
	mov QWORD PTR [r9+24], r15
	mov r15, r12
	xor r15, r11
	mov QWORD PTR [r9+72], r11
	mov r11, r13
	xor r11, rcx
	xor rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+96], rbp
	mov rbp, QWORD PTR [r9+128]
	xor rbp, r14
	mov QWORD PTR [r9+128], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+144]
	mov QWORD PTR [r9+152], rcx
	mov rcx, QWORD PTR [r9+144]
	xor rcx, QWORD PTR [r9+8]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+16]
	xor rcx, r15
	xor rbx, r11
	mov QWORD PTR [r9+16], rbx
	mov rbx, r10
	xor rbx, rax
	mov QWORD PTR [r9+32], rbx
	mov rbx, QWORD PTR [r9+120]
	xor rbx, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], rcx
	mov rcx, QWORD PTR [r9+64]
	xor rcx, QWORD PTR [r9+136]
	xor r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, QWORD PTR [r9+8]
	xor r10, rbp
	xor r12, rax
	xor r13, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+152]
	mov rax, QWORD PTR [r9+72]
	xor rax, QWORD PTR [r9+144]
	xor rbx, QWORD PTR [r9+128]
	xor r15, QWORD PTR [r9+96]
	xor r11, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rbx
	mov rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9+152]
	xor rbp, r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+16]
	mov QWORD PTR [r9+152], r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+32]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9]
	xor r10, QWORD PTR [r9+32]
	xor r10, QWORD PTR [r9]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rbx
	xor r12, QWORD PTR [r9]
	xor r14, r13
	xor r14, QWORD PTR [r9]
	xor r15, rbp
	xor r11, rcx
	xor r11, QWORD PTR [r9]
	mov r13, r15
	mov QWORD PTR [r9+80], r12
	mov r12, r11
	mov r11, rax
	mov QWORD PTR [r9+32], r10
	mov r10, QWORD PTR [r9+144]
	mov rbp, QWORD PTR [r9+80]
	mov rcx, QWORD PTR [r9+32]
	mov rbx, r14
	mov rax, QWORD PTR [r9+152]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+408]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+408]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+408]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+408]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+408]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+408]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+408]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+408]
	xor rax, r14
	mov r15, rax
	mov r14, rax
	xor r14, rbx
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov r14, rbx
	xor r14, rcx
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	mov r14, rcx
	xor r14, rbp
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	mov r14, rbp
	xor r14, r10
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	mov r14, r10
	xor r14, r11
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	mov r14, r11
	xor r14, r12
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	mov r14, r12
	xor r14, r13
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	mov r14, r13
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	xor r13, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r9+512], rax
	xor rbx, QWORD PTR [r9+520]
	mov QWORD PTR [r9+520], rbx
	xor rcx, QWORD PTR [r9+528]
	mov QWORD PTR [r9+528], rcx
	xor rbp, QWORD PTR [r9+536]
	mov QWORD PTR [r9+536], rbp
	xor r10, QWORD PTR [r9+544]
	mov QWORD PTR [r9+544], r10
	xor r11, QWORD PTR [r9+552]
	mov QWORD PTR [r9+552], r11
	xor r12, QWORD PTR [r9+560]
	mov QWORD PTR [r9+560], r12
	xor r13, QWORD PTR [r9+568]
	mov QWORD PTR [r9+568], r13
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [r9+3048], rax
	mov rax, QWORD PTR [r9+576]
	mov rbx, QWORD PTR [r9+584]
	mov rcx, QWORD PTR [r9+592]
	mov rbp, QWORD PTR [r9+600]
	mov r10, QWORD PTR [r9+608]
	mov r11, QWORD PTR [r9+616]
	mov r12, QWORD PTR [r9+624]
	mov r13, QWORD PTR [r9+632]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [r9+3056], rax
	add rsi, 128
	cmp r8, 2
	jae 25f
	mov rax, QWORD PTR [r9+3048]
	mov QWORD PTR [r9+3080], rax
	mov rax, QWORD PTR [r9+3056]
	mov QWORD PTR [r9+3088], rax
	jmp 26f
25:
	cmp r8, 3
	je 27f
	mov rax, QWORD PTR [r9+3048]
	mov QWORD PTR [r9+3064], rax
	mov rax, QWORD PTR [r9+3056]
	mov QWORD PTR [r9+3072], rax
	mov rax, QWORD PTR [r9+3032]
	xor rax, QWORD PTR [r9+3048]
	mov QWORD PTR [r9+3048], rax
	mov rax, QWORD PTR [r9+3040]
	xor rax, QWORD PTR [r9+3056]
	mov QWORD PTR [r9+3056], rax
	jmp 28f
27:
	mov rax, QWORD PTR [r9+3016]
	xor rax, QWORD PTR [r9+3048]
	mov QWORD PTR [r9+3048], rax
	mov rax, QWORD PTR [r9+3024]
	xor rax, QWORD PTR [r9+3056]
	mov QWORD PTR [r9+3056], rax
28:
26:
	sub r8, 1
	jne 24b
	mov rax, QWORD PTR [r9+3016]
	bswap rax
	mov rbx, QWORD PTR [r9+3024]
	bswap rbx
	mov rcx, QWORD PTR [r9+3032]
	bswap rcx
	mov rbp, QWORD PTR [r9+3040]
	bswap rbp
	mov r10, QWORD PTR [r9+3064]
	bswap r10
	mov r11, QWORD PTR [r9+3072]
	bswap r11
	mov r12, QWORD PTR [r9+3080]
	bswap r12
	mov r13, QWORD PTR [r9+3088]
	bswap r13
	mov r14, QWORD PTR [r9+2952]
	cmp r14, 16
	je 29f
	mov r14, rax
	bswap r14
	mov QWORD PTR [rdx], r14
	mov r14, rbx
	bswap r14
	mov QWORD PTR [rdx+8], r14
	mov r14, r12
	bswap r14
	mov QWORD PTR [rdx+16], r14
	mov r14, r13
	bswap r14
	mov QWORD PTR [rdx+24], r14
	mov r14, rcx
	shl r14, 15
	mov r15, rbp
	shr r15, 49
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+32], r14
	mov r14, rbp
	shl r14, 15
	mov r15, rcx
	shr r15, 49
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+40], r14
	mov r14, r10
	shl r14, 15
	mov r15, r11
	shr r15, 49
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+48], r14
	mov r14, r11
	shl r14, 15
	mov r15, r10
	shr r15, 49
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+56], r14
	mov r14, rcx
	shl r14, 30
	mov r15, rbp
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+64], r14
	mov r14, rbp
	shl r14, 30
	mov r15, rcx
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+72], r14
	mov r14, r12
	shl r14, 30
	mov r15, r13
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+80], r14
	mov r14, r13
	shl r14, 30
	mov r15, r12
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+88], r14
	mov r14, rax
	shl r14, 45
	mov r15, rbx
	shr r15, 19
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+96], r14
	mov r14, rbx
	shl r14, 45
	mov r15, rax
	shr r15, 19
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+104], r14
	mov r14, r10
	shl r14, 45
	mov r15, r11
	shr r15, 19
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+112], r14
	mov r14, r11
	shl r14, 45
	mov r15, r10
	shr r15, 19
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+120], r14
	mov r14, rax
	shl r14, 60
	mov r15, rbx
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+128], r14
	mov r14, rbx
	shl r14, 60
	mov r15, rax
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+136], r14
	mov r14, rcx
	shl r14, 60
	mov r15, rbp
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+144], r14
	mov r14, rbp
	shl r14, 60
	mov r15, rcx
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+152], r14
	mov r14, r12
	shl r14, 60
	mov r15, r13
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+160], r14
	mov r14, r13
	shl r14, 60
	mov r15, r12
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+168], r14
	mov r14, rbx
	shl r14, 13
	mov r15, rax
	shr r15, 51
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+176], r14
	mov r14, rax
	shl r14, 13
	mov r15, rbx
	shr r15, 51
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+184], r14
	mov r14, r11
	shl r14, 13
	mov r15, r10
	shr r15, 51
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+192], r14
	mov r14, r10
	shl r14, 13
	mov r15, r11
	shr r15, 51
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+200], r14
	mov r14, rbp
	shl r14, 30
	mov r15, rcx
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+208], r14
	mov r14, rcx
	shl r14, 30
	mov r15, rbp
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+216], r14
	mov r14, r11
	shl r14, 30
	mov r15, r10
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+224], r14
	mov r14, r10
	shl r14, 30
	mov r15, r11
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+232], r14
	mov r14, rbx
	shl r14, 47
	mov r15, rax
	shr r15, 17
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+240], r14
	mov r14, rax
	shl r14, 47
	mov r15, rbx
	shr r15, 17
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+248], r14
	mov r14, r13
	shl r14, 47
	mov r15, r12
	shr r15, 17
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+256], r14
	mov r14, r12
	shl r14, 47
	mov r15, r13
	shr r15, 17
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+264], r14
	jmp 210f
29:
	mov r14, rax
	bswap r14
	mov QWORD PTR [rdx], r14
	mov r14, rbx
	bswap r14
	mov QWORD PTR [rdx+8], r14
	mov r14, r10
	bswap r14
	mov QWORD PTR [rdx+16], r14
	mov r14, r11
	bswap r14
	mov QWORD PTR [rdx+24], r14
	mov r14, rax
	shl r14, 15
	mov r15, rbx
	shr r15, 49
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+32], r14
	mov r14, rbx
	shl r14, 15
	mov r15, rax
	shr r15, 49
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+40], r14
	mov r14, r10
	shl r14, 15
	mov r15, r11
	shr r15, 49
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+48], r14
	mov r14, r11
	shl r14, 15
	mov r15, r10
	shr r15, 49
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+56], r14
	mov r14, r10
	shl r14, 30
	mov r15, r11
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+64], r14
	mov r14, r11
	shl r14, 30
	mov r15, r10
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+72], r14
	mov r14, rax
	shl r14, 45
	mov r15, rbx
	shr r15, 19
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+80], r14
	mov r14, rbx
	shl r14, 45
	mov r15, rax
	shr r15, 19
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+88], r14
	mov r14, r10
	shl r14, 45
	mov r15, r11
	shr r15, 19
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+96], r14
	mov r14, rbx
	shl r14, 60
	mov r15, rax
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+104], r14
	mov r14, r10
	shl r14, 60
	mov r15, r11
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+112], r14
	mov r14, r11
	shl r14, 60
	mov r15, r10
	shr r15, 4
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+120], r14
	mov r14, rbx
	shl r14, 13
	mov r15, rax
	shr r15, 51
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+128], r14
	mov r14, rax
	shl r14, 13
	mov r15, rbx
	shr r15, 51
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+136], r14
	mov r14, rbx
	shl r14, 30
	mov r15, rax
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+144], r14
	mov r14, rax
	shl r14, 30
	mov r15, rbx
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+152], r14
	mov r14, r11
	shl r14, 30
	mov r15, r10
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+160], r14
	mov r14, r10
	shl r14, 30
	mov r15, r11
	shr r15, 34
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+168], r14
	mov r14, rbx
	shl r14, 47
	mov r15, rax
	shr r15, 17
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+176], r14
	mov r14, rax
	shl r14, 47
	mov r15, rbx
	shr r15, 17
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+184], r14
	mov r14, r11
	shl r14, 47
	mov r15, r10
	shr r15, 17
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+192], r14
	mov r14, r10
	shl r14, 47
	mov r15, r11
	shr r15, 17
	or r14, r15
	bswap r14
	mov QWORD PTR [rdx+200], r14
210:
	mov rbx, QWORD PTR [r9+2968]
	mov rbp, QWORD PTR [r9+2976]
	mov r12, QWORD PTR [r9+2984]
	mov r13, QWORD PTR [r9+2992]
	mov r14, QWORD PTR [r9+3000]
	mov r15, QWORD PTR [r9+3008]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	mov QWORD PTR [rsp+3208], r11
	lea rsp, [rsp+3216]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	lea rsp, [rsp-8]
	lea rsp, [rsp-3208]
	lea rsp, [rsp+3208]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_camellia_ecb_encrypt:
	lea rsp, [rsp-3216]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov r8, rcx
	mov QWORD PTR [r9+2968], rbx
	mov QWORD PTR [r9+2976], rbp
	mov QWORD PTR [r9+2984], r12
	mov QWORD PTR [r9+2992], r13
	mov QWORD PTR [r9+3000], r14
	mov QWORD PTR [r9+3008], r15
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+384], r14
	movabs r14, -71777214294589696
	mov QWORD PTR [r9+392], r14
	movabs r14, 72056494526300160
	mov QWORD PTR [r9+400], r14
	movabs r14, 16776960
	mov QWORD PTR [r9+408], r14
	movabs r14, 1099494850560
	mov QWORD PTR [r9+416], r14
	cmp rsi, 18
	je 20f
	mov rsi, r9
	add rsi, 768
	movabs r15, 34
22:
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	add rdi, 8
	sub r15, 1
	jne 22b
	mov rdi, r9
	add rdi, 2816
	jmp 21f
20:
	mov rsi, r9
	add rsi, 768
	movabs r15, 26
23:
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	add rdi, 8
	sub r15, 1
	jne 23b
	mov rdi, r9
	add rdi, 2304
21:
	test r8, r8
	je 24f
26:
	movabs rcx, 8
	cmp r8, 8
	jb 27f
	jmp 28f
27:
	mov rcx, r8
28:
	mov rax, rdx
	mov rbx, r9
	add rbx, 3016
29:
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	mov rbp, QWORD PTR [rax+8]
	mov QWORD PTR [rbx+8], rbp
	add rax, 16
	add rbx, 16
	sub rcx, 1
	jne 29b
	mov QWORD PTR [r9+2952], rdx
	mov QWORD PTR [r9+2960], r8
	mov QWORD PTR [r9+2944], rdi
	mov rdx, r9
	add rdx, 3016
	mov rsi, r9
	add rsi, 768
	mov rax, QWORD PTR [rdx+8]
	mov rbx, QWORD PTR [rdx+24]
	mov rcx, QWORD PTR [rdx+40]
	mov rbp, QWORD PTR [rdx+56]
	mov r10, QWORD PTR [rdx+72]
	mov r11, QWORD PTR [rdx+88]
	mov r12, QWORD PTR [rdx+104]
	mov r13, QWORD PTR [rdx+120]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [r9+576], rax
	mov QWORD PTR [r9+584], rbx
	mov QWORD PTR [r9+592], rcx
	mov QWORD PTR [r9+600], rbp
	mov QWORD PTR [r9+608], r10
	mov QWORD PTR [r9+616], r11
	mov QWORD PTR [r9+624], r12
	mov QWORD PTR [r9+632], r13
	mov rax, QWORD PTR [rdx]
	mov rbx, QWORD PTR [rdx+16]
	mov rcx, QWORD PTR [rdx+32]
	mov rbp, QWORD PTR [rdx+48]
	mov r10, QWORD PTR [rdx+64]
	mov r11, QWORD PTR [rdx+80]
	mov r12, QWORD PTR [rdx+96]
	mov r13, QWORD PTR [rdx+112]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov QWORD PTR [r9+512], rax
	mov QWORD PTR [r9+520], rbx
	mov QWORD PTR [r9+528], rcx
	mov QWORD PTR [r9+536], rbp
	mov QWORD PTR [r9+544], r10
	mov QWORD PTR [r9+552], r11
	mov QWORD PTR [r9+560], r12
	mov QWORD PTR [r9+568], r13
	mov r14, QWORD PTR [r9+576]
	xor r14, QWORD PTR [rsi+64]
	mov QWORD PTR [r9+576], r14
	mov r14, QWORD PTR [r9+584]
	xor r14, QWORD PTR [rsi+72]
	mov QWORD PTR [r9+584], r14
	mov r14, QWORD PTR [r9+592]
	xor r14, QWORD PTR [rsi+80]
	mov QWORD PTR [r9+592], r14
	mov r14, QWORD PTR [r9+600]
	xor r14, QWORD PTR [rsi+88]
	mov QWORD PTR [r9+600], r14
	mov r14, QWORD PTR [r9+608]
	xor r14, QWORD PTR [rsi+96]
	mov QWORD PTR [r9+608], r14
	mov r14, QWORD PTR [r9+616]
	xor r14, QWORD PTR [rsi+104]
	mov QWORD PTR [r9+616], r14
	mov r14, QWORD PTR [r9+624]
	xor r14, QWORD PTR [rsi+112]
	mov QWORD PTR [r9+624], r14
	mov r14, QWORD PTR [r9+632]
	xor r14, QWORD PTR [rsi+120]
	mov QWORD PTR [r9+632], r14
	add rsi, 128
210:
	mov rdi, rsi
	add rdi, 384
211:
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r13
	xor r14, rbx
	mov r15, r11
	xor r15, rbp
	mov QWORD PTR [r9+8], r11
	mov r11, rcx
	xor r11, r14
	mov QWORD PTR [r9+16], r14
	mov r14, r12
	xor r14, rax
	mov QWORD PTR [r9+24], rbp
	mov rbp, rax
	xor rbp, r15
	mov QWORD PTR [r9+32], rbp
	mov rbp, r10
	xor rbp, rbx
	mov QWORD PTR [r9+40], rbp
	mov rbp, r10
	xor rbp, r11
	mov QWORD PTR [r9+48], rbp
	mov rbp, r12
	xor rbp, r15
	mov QWORD PTR [r9+56], r15
	mov r15, rcx
	xor r15, r14
	mov QWORD PTR [r9+64], r15
	mov r15, r11
	xor r15, r14
	mov QWORD PTR [r9+72], r15
	mov r15, r13
	xor r15, r12
	mov QWORD PTR [r9+80], rbp
	mov rbp, r13
	xor rbp, r14
	xor rbp, QWORD PTR [r9]
	mov QWORD PTR [r9+88], rbp
	mov rbp, r12
	xor rbp, QWORD PTR [r9+24]
	mov QWORD PTR [r9+96], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, rbx
	mov QWORD PTR [r9+104], r12
	mov r12, QWORD PTR [r9+8]
	xor r12, rax
	mov QWORD PTR [r9+112], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, r11
	xor r14, r10
	xor r10, r15
	xor rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9]
	mov r15, rcx
	xor r15, QWORD PTR [r9+32]
	xor rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+80]
	xor r14, QWORD PTR [r9]
	mov QWORD PTR [r9+8], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov QWORD PTR [r9+120], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+40]
	mov QWORD PTR [r9+16], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+48]
	mov QWORD PTR [r9+128], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+72]
	mov QWORD PTR [r9+56], r14
	mov r14, r11
	xor r14, QWORD PTR [r9+32]
	xor r14, QWORD PTR [r9]
	xor r11, rbp
	xor r11, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+40]
	xor rbp, QWORD PTR [r9]
	xor r12, QWORD PTR [r9+48]
	xor r12, QWORD PTR [r9]
	mov QWORD PTR [r9+40], r11
	mov r11, QWORD PTR [r9+64]
	xor r11, QWORD PTR [r9+112]
	xor r11, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r9+96]
	xor rax, QWORD PTR [r9+104]
	xor rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9]
	mov QWORD PTR [r9+96], rbx
	mov rbx, rcx
	and rbx, r10
	mov QWORD PTR [r9+104], rcx
	mov rcx, rax
	and rcx, r11
	xor rcx, rbx
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [r9+48]
	and rax, r12
	xor rax, rbx
	mov rbx, r15
	and rbx, r14
	mov QWORD PTR [r9+32], r15
	mov r15, QWORD PTR [r9+16]
	and r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+136], r13
	mov r13, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+80]
	xor r13, rbx
	mov rbx, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+128]
	mov QWORD PTR [r9+144], r14
	mov r14, rbp
	and r14, QWORD PTR [r9+64]
	xor r14, rbx
	mov QWORD PTR [r9+152], rbp
	mov rbp, QWORD PTR [r9+8]
	and rbp, QWORD PTR [r9+88]
	xor rbp, rbx
	xor rcx, r14
	xor rax, rbp
	xor r15, r14
	xor r13, rbp
	xor rcx, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+120]
	xor r15, QWORD PTR [r9+96]
	xor r13, QWORD PTR [r9+40]
	mov rbp, rcx
	xor rbp, rax
	and rcx, r15
	mov r14, r13
	xor r14, rcx
	mov rbx, rbp
	and rbx, r14
	xor rbx, rax
	mov QWORD PTR [r9+40], r12
	mov r12, r15
	xor r12, r13
	xor rax, rcx
	and rax, r12
	xor rax, r13
	xor r15, rax
	mov r12, r14
	xor r12, rax
	and r13, r12
	xor r15, r13
	xor r14, r13
	and r14, rbx
	xor rbp, r14
	mov r14, rbp
	xor r14, r15
	mov r13, rbx
	xor r13, rax
	mov r12, rbx
	xor r12, rbp
	mov rcx, rax
	xor rcx, r15
	mov QWORD PTR [r9+96], rbx
	mov rbx, r13
	xor rbx, r14
	and r10, rcx
	and r11, r15
	mov QWORD PTR [r9+120], r10
	mov r10, rax
	and r10, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r10
	mov r10, r12
	and r10, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], r10
	mov r10, rbp
	and r10, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], r10
	mov r10, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, r13
	and r10, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r10
	mov r10, rbx
	and r10, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r10
	mov r10, r14
	and r10, QWORD PTR [r9+88]
	and rcx, QWORD PTR [r9+104]
	and r15, QWORD PTR [r9+112]
	and rax, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	and rbp, QWORD PTR [r9+16]
	mov QWORD PTR [r9+16], rbp
	mov rbp, QWORD PTR [r9+96]
	and rbp, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+152]
	and r14, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], r15
	mov r15, r11
	xor r15, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r11
	mov r11, QWORD PTR [r9+144]
	xor r11, QWORD PTR [r9+80]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+128]
	xor rcx, r10
	mov QWORD PTR [r9+152], r10
	mov r10, QWORD PTR [r9+120]
	xor r10, rbx
	xor rax, r15
	mov QWORD PTR [r9+24], r15
	mov r15, r12
	xor r15, r11
	mov QWORD PTR [r9+72], r11
	mov r11, r13
	xor r11, rcx
	xor rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+96], rbp
	mov rbp, QWORD PTR [r9+128]
	xor rbp, r14
	mov QWORD PTR [r9+128], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+144]
	mov QWORD PTR [r9+152], rcx
	mov rcx, QWORD PTR [r9+144]
	xor rcx, QWORD PTR [r9+8]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+16]
	xor rcx, r15
	xor rbx, r11
	mov QWORD PTR [r9+16], rbx
	mov rbx, r10
	xor rbx, rax
	mov QWORD PTR [r9+32], rbx
	mov rbx, QWORD PTR [r9+120]
	xor rbx, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], rcx
	mov rcx, QWORD PTR [r9+64]
	xor rcx, QWORD PTR [r9+136]
	xor r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, QWORD PTR [r9+8]
	xor r10, rbp
	xor r12, rax
	xor r13, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+152]
	mov rax, QWORD PTR [r9+72]
	xor rax, QWORD PTR [r9+144]
	xor rbx, QWORD PTR [r9+128]
	xor r15, QWORD PTR [r9+96]
	xor r11, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rbx
	mov rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9+152]
	xor rbp, r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+16]
	mov QWORD PTR [r9+152], r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+32]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9]
	xor r10, QWORD PTR [r9+32]
	xor r10, QWORD PTR [r9]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rbx
	xor r12, QWORD PTR [r9]
	xor r14, r13
	xor r14, QWORD PTR [r9]
	xor r15, rbp
	xor r11, rcx
	xor r11, QWORD PTR [r9]
	mov r13, r15
	mov QWORD PTR [r9+80], r12
	mov r12, r11
	mov r11, rax
	mov QWORD PTR [r9+32], r10
	mov r10, QWORD PTR [r9+144]
	mov rbp, QWORD PTR [r9+80]
	mov rcx, QWORD PTR [r9+32]
	mov rbx, r14
	mov rax, QWORD PTR [r9+152]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+408]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+408]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+408]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+408]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+408]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+408]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+408]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+408]
	xor rax, r14
	mov r15, rax
	mov r14, rax
	xor r14, rbx
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov r14, rbx
	xor r14, rcx
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	mov r14, rcx
	xor r14, rbp
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	mov r14, rbp
	xor r14, r10
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	mov r14, r10
	xor r14, r11
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	mov r14, r11
	xor r14, r12
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	mov r14, r12
	xor r14, r13
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	mov r14, r13
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	xor r13, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	xor rax, QWORD PTR [r9+576]
	mov QWORD PTR [r9+576], rax
	xor rbx, QWORD PTR [r9+584]
	mov QWORD PTR [r9+584], rbx
	xor rcx, QWORD PTR [r9+592]
	mov QWORD PTR [r9+592], rcx
	xor rbp, QWORD PTR [r9+600]
	mov QWORD PTR [r9+600], rbp
	xor r10, QWORD PTR [r9+608]
	mov QWORD PTR [r9+608], r10
	xor r11, QWORD PTR [r9+616]
	mov QWORD PTR [r9+616], r11
	xor r12, QWORD PTR [r9+624]
	mov QWORD PTR [r9+624], r12
	xor r13, QWORD PTR [r9+632]
	mov QWORD PTR [r9+632], r13
	xor rax, QWORD PTR [rsi+64]
	xor rbx, QWORD PTR [rsi+72]
	xor rcx, QWORD PTR [rsi+80]
	xor rbp, QWORD PTR [rsi+88]
	xor r10, QWORD PTR [rsi+96]
	xor r11, QWORD PTR [rsi+104]
	xor r12, QWORD PTR [rsi+112]
	xor r13, QWORD PTR [rsi+120]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r13
	xor r14, rbx
	mov r15, r11
	xor r15, rbp
	mov QWORD PTR [r9+8], r11
	mov r11, rcx
	xor r11, r14
	mov QWORD PTR [r9+16], r14
	mov r14, r12
	xor r14, rax
	mov QWORD PTR [r9+24], rbp
	mov rbp, rax
	xor rbp, r15
	mov QWORD PTR [r9+32], rbp
	mov rbp, r10
	xor rbp, rbx
	mov QWORD PTR [r9+40], rbp
	mov rbp, r10
	xor rbp, r11
	mov QWORD PTR [r9+48], rbp
	mov rbp, r12
	xor rbp, r15
	mov QWORD PTR [r9+56], r15
	mov r15, rcx
	xor r15, r14
	mov QWORD PTR [r9+64], r15
	mov r15, r11
	xor r15, r14
	mov QWORD PTR [r9+72], r15
	mov r15, r13
	xor r15, r12
	mov QWORD PTR [r9+80], rbp
	mov rbp, r13
	xor rbp, r14
	xor rbp, QWORD PTR [r9]
	mov QWORD PTR [r9+88], rbp
	mov rbp, r12
	xor rbp, QWORD PTR [r9+24]
	mov QWORD PTR [r9+96], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, rbx
	mov QWORD PTR [r9+104], r12
	mov r12, QWORD PTR [r9+8]
	xor r12, rax
	mov QWORD PTR [r9+112], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, r11
	xor r14, r10
	xor r10, r15
	xor rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9]
	mov r15, rcx
	xor r15, QWORD PTR [r9+32]
	xor rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+80]
	xor r14, QWORD PTR [r9]
	mov QWORD PTR [r9+8], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov QWORD PTR [r9+120], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+40]
	mov QWORD PTR [r9+16], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+48]
	mov QWORD PTR [r9+128], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+72]
	mov QWORD PTR [r9+56], r14
	mov r14, r11
	xor r14, QWORD PTR [r9+32]
	xor r14, QWORD PTR [r9]
	xor r11, rbp
	xor r11, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+40]
	xor rbp, QWORD PTR [r9]
	xor r12, QWORD PTR [r9+48]
	xor r12, QWORD PTR [r9]
	mov QWORD PTR [r9+40], r11
	mov r11, QWORD PTR [r9+64]
	xor r11, QWORD PTR [r9+112]
	xor r11, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r9+96]
	xor rax, QWORD PTR [r9+104]
	xor rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9]
	mov QWORD PTR [r9+96], rbx
	mov rbx, rcx
	and rbx, r10
	mov QWORD PTR [r9+104], rcx
	mov rcx, rax
	and rcx, r11
	xor rcx, rbx
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [r9+48]
	and rax, r12
	xor rax, rbx
	mov rbx, r15
	and rbx, r14
	mov QWORD PTR [r9+32], r15
	mov r15, QWORD PTR [r9+16]
	and r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+136], r13
	mov r13, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+80]
	xor r13, rbx
	mov rbx, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+128]
	mov QWORD PTR [r9+144], r14
	mov r14, rbp
	and r14, QWORD PTR [r9+64]
	xor r14, rbx
	mov QWORD PTR [r9+152], rbp
	mov rbp, QWORD PTR [r9+8]
	and rbp, QWORD PTR [r9+88]
	xor rbp, rbx
	xor rcx, r14
	xor rax, rbp
	xor r15, r14
	xor r13, rbp
	xor rcx, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+120]
	xor r15, QWORD PTR [r9+96]
	xor r13, QWORD PTR [r9+40]
	mov rbp, rcx
	xor rbp, rax
	and rcx, r15
	mov r14, r13
	xor r14, rcx
	mov rbx, rbp
	and rbx, r14
	xor rbx, rax
	mov QWORD PTR [r9+40], r12
	mov r12, r15
	xor r12, r13
	xor rax, rcx
	and rax, r12
	xor rax, r13
	xor r15, rax
	mov r12, r14
	xor r12, rax
	and r13, r12
	xor r15, r13
	xor r14, r13
	and r14, rbx
	xor rbp, r14
	mov r14, rbp
	xor r14, r15
	mov r13, rbx
	xor r13, rax
	mov r12, rbx
	xor r12, rbp
	mov rcx, rax
	xor rcx, r15
	mov QWORD PTR [r9+96], rbx
	mov rbx, r13
	xor rbx, r14
	and r10, rcx
	and r11, r15
	mov QWORD PTR [r9+120], r10
	mov r10, rax
	and r10, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r10
	mov r10, r12
	and r10, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], r10
	mov r10, rbp
	and r10, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], r10
	mov r10, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, r13
	and r10, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r10
	mov r10, rbx
	and r10, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r10
	mov r10, r14
	and r10, QWORD PTR [r9+88]
	and rcx, QWORD PTR [r9+104]
	and r15, QWORD PTR [r9+112]
	and rax, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	and rbp, QWORD PTR [r9+16]
	mov QWORD PTR [r9+16], rbp
	mov rbp, QWORD PTR [r9+96]
	and rbp, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+152]
	and r14, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], r15
	mov r15, r11
	xor r15, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r11
	mov r11, QWORD PTR [r9+144]
	xor r11, QWORD PTR [r9+80]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+128]
	xor rcx, r10
	mov QWORD PTR [r9+152], r10
	mov r10, QWORD PTR [r9+120]
	xor r10, rbx
	xor rax, r15
	mov QWORD PTR [r9+24], r15
	mov r15, r12
	xor r15, r11
	mov QWORD PTR [r9+72], r11
	mov r11, r13
	xor r11, rcx
	xor rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+96], rbp
	mov rbp, QWORD PTR [r9+128]
	xor rbp, r14
	mov QWORD PTR [r9+128], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+144]
	mov QWORD PTR [r9+152], rcx
	mov rcx, QWORD PTR [r9+144]
	xor rcx, QWORD PTR [r9+8]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+16]
	xor rcx, r15
	xor rbx, r11
	mov QWORD PTR [r9+16], rbx
	mov rbx, r10
	xor rbx, rax
	mov QWORD PTR [r9+32], rbx
	mov rbx, QWORD PTR [r9+120]
	xor rbx, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], rcx
	mov rcx, QWORD PTR [r9+64]
	xor rcx, QWORD PTR [r9+136]
	xor r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, QWORD PTR [r9+8]
	xor r10, rbp
	xor r12, rax
	xor r13, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+152]
	mov rax, QWORD PTR [r9+72]
	xor rax, QWORD PTR [r9+144]
	xor rbx, QWORD PTR [r9+128]
	xor r15, QWORD PTR [r9+96]
	xor r11, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rbx
	mov rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9+152]
	xor rbp, r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+16]
	mov QWORD PTR [r9+152], r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+32]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9]
	xor r10, QWORD PTR [r9+32]
	xor r10, QWORD PTR [r9]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rbx
	xor r12, QWORD PTR [r9]
	xor r14, r13
	xor r14, QWORD PTR [r9]
	xor r15, rbp
	xor r11, rcx
	xor r11, QWORD PTR [r9]
	mov r13, r15
	mov QWORD PTR [r9+80], r12
	mov r12, r11
	mov r11, rax
	mov QWORD PTR [r9+32], r10
	mov r10, QWORD PTR [r9+144]
	mov rbp, QWORD PTR [r9+80]
	mov rcx, QWORD PTR [r9+32]
	mov rbx, r14
	mov rax, QWORD PTR [r9+152]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+408]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+408]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+408]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+408]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+408]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+408]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+408]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+408]
	xor rax, r14
	mov r15, rax
	mov r14, rax
	xor r14, rbx
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov r14, rbx
	xor r14, rcx
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	mov r14, rcx
	xor r14, rbp
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	mov r14, rbp
	xor r14, r10
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	mov r14, r10
	xor r14, r11
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	mov r14, r11
	xor r14, r12
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	mov r14, r12
	xor r14, r13
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	mov r14, r13
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	xor r13, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r9+512], rax
	xor rbx, QWORD PTR [r9+520]
	mov QWORD PTR [r9+520], rbx
	xor rcx, QWORD PTR [r9+528]
	mov QWORD PTR [r9+528], rcx
	xor rbp, QWORD PTR [r9+536]
	mov QWORD PTR [r9+536], rbp
	xor r10, QWORD PTR [r9+544]
	mov QWORD PTR [r9+544], r10
	xor r11, QWORD PTR [r9+552]
	mov QWORD PTR [r9+552], r11
	xor r12, QWORD PTR [r9+560]
	mov QWORD PTR [r9+560], r12
	xor r13, QWORD PTR [r9+568]
	mov QWORD PTR [r9+568], r13
	add rsi, 128
	cmp rsi, rdi
	jne 211b
	mov r14, QWORD PTR [r9+2944]
	cmp rsi, r14
	jne 212f
	jmp 213f
212:
	mov rax, QWORD PTR [r9+576]
	mov rbx, QWORD PTR [r9+584]
	mov rcx, QWORD PTR [r9+592]
	mov rbp, QWORD PTR [r9+600]
	mov r10, QWORD PTR [r9+608]
	mov r11, QWORD PTR [r9+616]
	mov r12, QWORD PTR [r9+624]
	mov r13, QWORD PTR [r9+632]
	mov r14, r13
	or r14, QWORD PTR [rsi+120]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r12
	or r14, QWORD PTR [rsi+112]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r11
	or r14, QWORD PTR [rsi+104]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r10
	or r14, QWORD PTR [rsi+96]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, rbp
	or r14, QWORD PTR [rsi+88]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rcx
	or r14, QWORD PTR [rsi+80]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbx
	or r14, QWORD PTR [rsi+72]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rax
	or r14, QWORD PTR [rsi+64]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r15, r13
	mov r14, r12
	and r14, QWORD PTR [rsi+112]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r11
	and r14, QWORD PTR [rsi+104]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r10
	and r14, QWORD PTR [rsi+96]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, rbp
	and r14, QWORD PTR [rsi+88]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, rcx
	and r14, QWORD PTR [rsi+80]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbx
	and r14, QWORD PTR [rsi+72]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rax
	and r14, QWORD PTR [rsi+64]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, r15
	and r14, QWORD PTR [rsi+120]
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov QWORD PTR [r9+576], rax
	mov QWORD PTR [r9+584], rbx
	mov QWORD PTR [r9+592], rcx
	mov QWORD PTR [r9+600], rbp
	mov QWORD PTR [r9+608], r10
	mov QWORD PTR [r9+616], r11
	mov QWORD PTR [r9+624], r12
	mov QWORD PTR [r9+632], r13
	mov rax, QWORD PTR [r9+512]
	mov rbx, QWORD PTR [r9+520]
	mov rcx, QWORD PTR [r9+528]
	mov rbp, QWORD PTR [r9+536]
	mov r10, QWORD PTR [r9+544]
	mov r11, QWORD PTR [r9+552]
	mov r12, QWORD PTR [r9+560]
	mov r13, QWORD PTR [r9+568]
	mov r15, r13
	mov r14, r12
	and r14, QWORD PTR [rsi+48]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r11
	and r14, QWORD PTR [rsi+40]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r10
	and r14, QWORD PTR [rsi+32]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, rbp
	and r14, QWORD PTR [rsi+24]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, rcx
	and r14, QWORD PTR [rsi+16]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbx
	and r14, QWORD PTR [rsi+8]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rax
	and r14, QWORD PTR [rsi]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, r15
	and r14, QWORD PTR [rsi+56]
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, r13
	or r14, QWORD PTR [rsi+56]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r12
	or r14, QWORD PTR [rsi+48]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r11
	or r14, QWORD PTR [rsi+40]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r10
	or r14, QWORD PTR [rsi+32]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, rbp
	or r14, QWORD PTR [rsi+24]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rcx
	or r14, QWORD PTR [rsi+16]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbx
	or r14, QWORD PTR [rsi+8]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rax
	or r14, QWORD PTR [rsi]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov QWORD PTR [r9+512], rax
	mov QWORD PTR [r9+520], rbx
	mov QWORD PTR [r9+528], rcx
	mov QWORD PTR [r9+536], rbp
	mov QWORD PTR [r9+544], r10
	mov QWORD PTR [r9+552], r11
	mov QWORD PTR [r9+560], r12
	mov QWORD PTR [r9+568], r13
	add rsi, 128
213:
	mov r14, QWORD PTR [r9+2944]
	cmp rsi, r14
	jne 210b
	xor rax, QWORD PTR [rsi+64]
	xor rbx, QWORD PTR [rsi+72]
	xor rcx, QWORD PTR [rsi+80]
	xor rbp, QWORD PTR [rsi+88]
	xor r10, QWORD PTR [rsi+96]
	xor r11, QWORD PTR [rsi+104]
	xor r12, QWORD PTR [rsi+112]
	xor r13, QWORD PTR [rsi+120]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rdx+8], rax
	mov QWORD PTR [rdx+24], rbx
	mov QWORD PTR [rdx+40], rcx
	mov QWORD PTR [rdx+56], rbp
	mov QWORD PTR [rdx+72], r10
	mov QWORD PTR [rdx+88], r11
	mov QWORD PTR [rdx+104], r12
	mov QWORD PTR [rdx+120], r13
	mov rax, QWORD PTR [r9+576]
	mov rbx, QWORD PTR [r9+584]
	mov rcx, QWORD PTR [r9+592]
	mov rbp, QWORD PTR [r9+600]
	mov r10, QWORD PTR [r9+608]
	mov r11, QWORD PTR [r9+616]
	mov r12, QWORD PTR [r9+624]
	mov r13, QWORD PTR [r9+632]
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+16], rbx
	mov QWORD PTR [rdx+32], rcx
	mov QWORD PTR [rdx+48], rbp
	mov QWORD PTR [rdx+64], r10
	mov QWORD PTR [rdx+80], r11
	mov QWORD PTR [rdx+96], r12
	mov QWORD PTR [rdx+112], r13
	mov rdx, QWORD PTR [r9+2952]
	mov r8, QWORD PTR [r9+2960]
	mov rdi, QWORD PTR [r9+2944]
	movabs rcx, 8
	cmp r8, 8
	jb 214f
	jmp 215f
214:
	mov rcx, r8
215:
	mov rax, r9
	add rax, 3016
	mov rbx, rdx
216:
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	mov rbp, QWORD PTR [rax+8]
	mov QWORD PTR [rbx+8], rbp
	add rax, 16
	add rbx, 16
	sub rcx, 1
	jne 216b
	cmp r8, 8
	jb 217f
	add rdx, 128
	sub r8, 8
	jmp 218f
217:
	sub r8, r8
218:
	jne 26b
	jmp 25f
24:
25:
	mov rbx, QWORD PTR [r9+2968]
	mov rbp, QWORD PTR [r9+2976]
	mov r12, QWORD PTR [r9+2984]
	mov r13, QWORD PTR [r9+2992]
	mov r14, QWORD PTR [r9+3000]
	mov r15, QWORD PTR [r9+3008]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	mov QWORD PTR [rsp+3208], r11
	lea rsp, [rsp+3216]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	lea rsp, [rsp-3208]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3208]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_camellia_ecb_decrypt:
	lea rsp, [rsp-3216]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov r8, rcx
	mov QWORD PTR [r9+2968], rbx
	mov QWORD PTR [r9+2976], rbp
	mov QWORD PTR [r9+2984], r12
	mov QWORD PTR [r9+2992], r13
	mov QWORD PTR [r9+3000], r14
	mov QWORD PTR [r9+3008], r15
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+384], r14
	movabs r14, -71777214294589696
	mov QWORD PTR [r9+392], r14
	movabs r14, 72056494526300160
	mov QWORD PTR [r9+400], r14
	movabs r14, 16776960
	mov QWORD PTR [r9+408], r14
	movabs r14, 1099494850560
	mov QWORD PTR [r9+416], r14
	cmp rsi, 18
	je 20f
	mov rsi, r9
	add rsi, 768
	add rdi, 256
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	mov rax, QWORD PTR [rdi+8]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	sub rdi, 8
	movabs r15, 30
22:
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	sub rdi, 8
	sub r15, 1
	jne 22b
	sub rdi, 8
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	mov rax, QWORD PTR [rdi+8]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	mov rdi, r9
	add rdi, 2816
	jmp 21f
20:
	mov rsi, r9
	add rsi, 768
	add rdi, 192
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	mov rax, QWORD PTR [rdi+8]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	sub rdi, 8
	movabs r15, 22
23:
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	sub rdi, 8
	sub r15, 1
	jne 23b
	sub rdi, 8
	mov rax, QWORD PTR [rdi]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	mov rax, QWORD PTR [rdi+8]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	mov rdi, r9
	add rdi, 2304
21:
	test r8, r8
	je 24f
26:
	movabs rcx, 8
	cmp r8, 8
	jb 27f
	jmp 28f
27:
	mov rcx, r8
28:
	mov rax, rdx
	mov rbx, r9
	add rbx, 3016
29:
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	mov rbp, QWORD PTR [rax+8]
	mov QWORD PTR [rbx+8], rbp
	add rax, 16
	add rbx, 16
	sub rcx, 1
	jne 29b
	mov QWORD PTR [r9+2952], rdx
	mov QWORD PTR [r9+2960], r8
	mov QWORD PTR [r9+2944], rdi
	mov rdx, r9
	add rdx, 3016
	mov rsi, r9
	add rsi, 768
	mov rax, QWORD PTR [rdx+8]
	mov rbx, QWORD PTR [rdx+24]
	mov rcx, QWORD PTR [rdx+40]
	mov rbp, QWORD PTR [rdx+56]
	mov r10, QWORD PTR [rdx+72]
	mov r11, QWORD PTR [rdx+88]
	mov r12, QWORD PTR [rdx+104]
	mov r13, QWORD PTR [rdx+120]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [r9+576], rax
	mov QWORD PTR [r9+584], rbx
	mov QWORD PTR [r9+592], rcx
	mov QWORD PTR [r9+600], rbp
	mov QWORD PTR [r9+608], r10
	mov QWORD PTR [r9+616], r11
	mov QWORD PTR [r9+624], r12
	mov QWORD PTR [r9+632], r13
	mov rax, QWORD PTR [rdx]
	mov rbx, QWORD PTR [rdx+16]
	mov rcx, QWORD PTR [rdx+32]
	mov rbp, QWORD PTR [rdx+48]
	mov r10, QWORD PTR [rdx+64]
	mov r11, QWORD PTR [rdx+80]
	mov r12, QWORD PTR [rdx+96]
	mov r13, QWORD PTR [rdx+112]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov QWORD PTR [r9+512], rax
	mov QWORD PTR [r9+520], rbx
	mov QWORD PTR [r9+528], rcx
	mov QWORD PTR [r9+536], rbp
	mov QWORD PTR [r9+544], r10
	mov QWORD PTR [r9+552], r11
	mov QWORD PTR [r9+560], r12
	mov QWORD PTR [r9+568], r13
	mov r14, QWORD PTR [r9+576]
	xor r14, QWORD PTR [rsi+64]
	mov QWORD PTR [r9+576], r14
	mov r14, QWORD PTR [r9+584]
	xor r14, QWORD PTR [rsi+72]
	mov QWORD PTR [r9+584], r14
	mov r14, QWORD PTR [r9+592]
	xor r14, QWORD PTR [rsi+80]
	mov QWORD PTR [r9+592], r14
	mov r14, QWORD PTR [r9+600]
	xor r14, QWORD PTR [rsi+88]
	mov QWORD PTR [r9+600], r14
	mov r14, QWORD PTR [r9+608]
	xor r14, QWORD PTR [rsi+96]
	mov QWORD PTR [r9+608], r14
	mov r14, QWORD PTR [r9+616]
	xor r14, QWORD PTR [rsi+104]
	mov QWORD PTR [r9+616], r14
	mov r14, QWORD PTR [r9+624]
	xor r14, QWORD PTR [rsi+112]
	mov QWORD PTR [r9+624], r14
	mov r14, QWORD PTR [r9+632]
	xor r14, QWORD PTR [rsi+120]
	mov QWORD PTR [r9+632], r14
	add rsi, 128
210:
	mov rdi, rsi
	add rdi, 384
211:
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r13
	xor r14, rbx
	mov r15, r11
	xor r15, rbp
	mov QWORD PTR [r9+8], r11
	mov r11, rcx
	xor r11, r14
	mov QWORD PTR [r9+16], r14
	mov r14, r12
	xor r14, rax
	mov QWORD PTR [r9+24], rbp
	mov rbp, rax
	xor rbp, r15
	mov QWORD PTR [r9+32], rbp
	mov rbp, r10
	xor rbp, rbx
	mov QWORD PTR [r9+40], rbp
	mov rbp, r10
	xor rbp, r11
	mov QWORD PTR [r9+48], rbp
	mov rbp, r12
	xor rbp, r15
	mov QWORD PTR [r9+56], r15
	mov r15, rcx
	xor r15, r14
	mov QWORD PTR [r9+64], r15
	mov r15, r11
	xor r15, r14
	mov QWORD PTR [r9+72], r15
	mov r15, r13
	xor r15, r12
	mov QWORD PTR [r9+80], rbp
	mov rbp, r13
	xor rbp, r14
	xor rbp, QWORD PTR [r9]
	mov QWORD PTR [r9+88], rbp
	mov rbp, r12
	xor rbp, QWORD PTR [r9+24]
	mov QWORD PTR [r9+96], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, rbx
	mov QWORD PTR [r9+104], r12
	mov r12, QWORD PTR [r9+8]
	xor r12, rax
	mov QWORD PTR [r9+112], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, r11
	xor r14, r10
	xor r10, r15
	xor rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9]
	mov r15, rcx
	xor r15, QWORD PTR [r9+32]
	xor rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+80]
	xor r14, QWORD PTR [r9]
	mov QWORD PTR [r9+8], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov QWORD PTR [r9+120], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+40]
	mov QWORD PTR [r9+16], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+48]
	mov QWORD PTR [r9+128], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+72]
	mov QWORD PTR [r9+56], r14
	mov r14, r11
	xor r14, QWORD PTR [r9+32]
	xor r14, QWORD PTR [r9]
	xor r11, rbp
	xor r11, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+40]
	xor rbp, QWORD PTR [r9]
	xor r12, QWORD PTR [r9+48]
	xor r12, QWORD PTR [r9]
	mov QWORD PTR [r9+40], r11
	mov r11, QWORD PTR [r9+64]
	xor r11, QWORD PTR [r9+112]
	xor r11, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r9+96]
	xor rax, QWORD PTR [r9+104]
	xor rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9]
	mov QWORD PTR [r9+96], rbx
	mov rbx, rcx
	and rbx, r10
	mov QWORD PTR [r9+104], rcx
	mov rcx, rax
	and rcx, r11
	xor rcx, rbx
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [r9+48]
	and rax, r12
	xor rax, rbx
	mov rbx, r15
	and rbx, r14
	mov QWORD PTR [r9+32], r15
	mov r15, QWORD PTR [r9+16]
	and r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+136], r13
	mov r13, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+80]
	xor r13, rbx
	mov rbx, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+128]
	mov QWORD PTR [r9+144], r14
	mov r14, rbp
	and r14, QWORD PTR [r9+64]
	xor r14, rbx
	mov QWORD PTR [r9+152], rbp
	mov rbp, QWORD PTR [r9+8]
	and rbp, QWORD PTR [r9+88]
	xor rbp, rbx
	xor rcx, r14
	xor rax, rbp
	xor r15, r14
	xor r13, rbp
	xor rcx, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+120]
	xor r15, QWORD PTR [r9+96]
	xor r13, QWORD PTR [r9+40]
	mov rbp, rcx
	xor rbp, rax
	and rcx, r15
	mov r14, r13
	xor r14, rcx
	mov rbx, rbp
	and rbx, r14
	xor rbx, rax
	mov QWORD PTR [r9+40], r12
	mov r12, r15
	xor r12, r13
	xor rax, rcx
	and rax, r12
	xor rax, r13
	xor r15, rax
	mov r12, r14
	xor r12, rax
	and r13, r12
	xor r15, r13
	xor r14, r13
	and r14, rbx
	xor rbp, r14
	mov r14, rbp
	xor r14, r15
	mov r13, rbx
	xor r13, rax
	mov r12, rbx
	xor r12, rbp
	mov rcx, rax
	xor rcx, r15
	mov QWORD PTR [r9+96], rbx
	mov rbx, r13
	xor rbx, r14
	and r10, rcx
	and r11, r15
	mov QWORD PTR [r9+120], r10
	mov r10, rax
	and r10, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r10
	mov r10, r12
	and r10, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], r10
	mov r10, rbp
	and r10, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], r10
	mov r10, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, r13
	and r10, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r10
	mov r10, rbx
	and r10, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r10
	mov r10, r14
	and r10, QWORD PTR [r9+88]
	and rcx, QWORD PTR [r9+104]
	and r15, QWORD PTR [r9+112]
	and rax, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	and rbp, QWORD PTR [r9+16]
	mov QWORD PTR [r9+16], rbp
	mov rbp, QWORD PTR [r9+96]
	and rbp, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+152]
	and r14, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], r15
	mov r15, r11
	xor r15, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r11
	mov r11, QWORD PTR [r9+144]
	xor r11, QWORD PTR [r9+80]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+128]
	xor rcx, r10
	mov QWORD PTR [r9+152], r10
	mov r10, QWORD PTR [r9+120]
	xor r10, rbx
	xor rax, r15
	mov QWORD PTR [r9+24], r15
	mov r15, r12
	xor r15, r11
	mov QWORD PTR [r9+72], r11
	mov r11, r13
	xor r11, rcx
	xor rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+96], rbp
	mov rbp, QWORD PTR [r9+128]
	xor rbp, r14
	mov QWORD PTR [r9+128], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+144]
	mov QWORD PTR [r9+152], rcx
	mov rcx, QWORD PTR [r9+144]
	xor rcx, QWORD PTR [r9+8]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+16]
	xor rcx, r15
	xor rbx, r11
	mov QWORD PTR [r9+16], rbx
	mov rbx, r10
	xor rbx, rax
	mov QWORD PTR [r9+32], rbx
	mov rbx, QWORD PTR [r9+120]
	xor rbx, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], rcx
	mov rcx, QWORD PTR [r9+64]
	xor rcx, QWORD PTR [r9+136]
	xor r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, QWORD PTR [r9+8]
	xor r10, rbp
	xor r12, rax
	xor r13, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+152]
	mov rax, QWORD PTR [r9+72]
	xor rax, QWORD PTR [r9+144]
	xor rbx, QWORD PTR [r9+128]
	xor r15, QWORD PTR [r9+96]
	xor r11, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rbx
	mov rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9+152]
	xor rbp, r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+16]
	mov QWORD PTR [r9+152], r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+32]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9]
	xor r10, QWORD PTR [r9+32]
	xor r10, QWORD PTR [r9]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rbx
	xor r12, QWORD PTR [r9]
	xor r14, r13
	xor r14, QWORD PTR [r9]
	xor r15, rbp
	xor r11, rcx
	xor r11, QWORD PTR [r9]
	mov r13, r15
	mov QWORD PTR [r9+80], r12
	mov r12, r11
	mov r11, rax
	mov QWORD PTR [r9+32], r10
	mov r10, QWORD PTR [r9+144]
	mov rbp, QWORD PTR [r9+80]
	mov rcx, QWORD PTR [r9+32]
	mov rbx, r14
	mov rax, QWORD PTR [r9+152]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+408]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+408]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+408]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+408]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+408]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+408]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+408]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+408]
	xor rax, r14
	mov r15, rax
	mov r14, rax
	xor r14, rbx
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov r14, rbx
	xor r14, rcx
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	mov r14, rcx
	xor r14, rbp
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	mov r14, rbp
	xor r14, r10
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	mov r14, r10
	xor r14, r11
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	mov r14, r11
	xor r14, r12
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	mov r14, r12
	xor r14, r13
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	mov r14, r13
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	xor r13, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	xor rax, QWORD PTR [r9+576]
	mov QWORD PTR [r9+576], rax
	xor rbx, QWORD PTR [r9+584]
	mov QWORD PTR [r9+584], rbx
	xor rcx, QWORD PTR [r9+592]
	mov QWORD PTR [r9+592], rcx
	xor rbp, QWORD PTR [r9+600]
	mov QWORD PTR [r9+600], rbp
	xor r10, QWORD PTR [r9+608]
	mov QWORD PTR [r9+608], r10
	xor r11, QWORD PTR [r9+616]
	mov QWORD PTR [r9+616], r11
	xor r12, QWORD PTR [r9+624]
	mov QWORD PTR [r9+624], r12
	xor r13, QWORD PTR [r9+632]
	mov QWORD PTR [r9+632], r13
	xor rax, QWORD PTR [rsi+64]
	xor rbx, QWORD PTR [rsi+72]
	xor rcx, QWORD PTR [rsi+80]
	xor rbp, QWORD PTR [rsi+88]
	xor r10, QWORD PTR [rsi+96]
	xor r11, QWORD PTR [rsi+104]
	xor r12, QWORD PTR [rsi+112]
	xor r13, QWORD PTR [rsi+120]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r13
	xor r14, rbx
	mov r15, r11
	xor r15, rbp
	mov QWORD PTR [r9+8], r11
	mov r11, rcx
	xor r11, r14
	mov QWORD PTR [r9+16], r14
	mov r14, r12
	xor r14, rax
	mov QWORD PTR [r9+24], rbp
	mov rbp, rax
	xor rbp, r15
	mov QWORD PTR [r9+32], rbp
	mov rbp, r10
	xor rbp, rbx
	mov QWORD PTR [r9+40], rbp
	mov rbp, r10
	xor rbp, r11
	mov QWORD PTR [r9+48], rbp
	mov rbp, r12
	xor rbp, r15
	mov QWORD PTR [r9+56], r15
	mov r15, rcx
	xor r15, r14
	mov QWORD PTR [r9+64], r15
	mov r15, r11
	xor r15, r14
	mov QWORD PTR [r9+72], r15
	mov r15, r13
	xor r15, r12
	mov QWORD PTR [r9+80], rbp
	mov rbp, r13
	xor rbp, r14
	xor rbp, QWORD PTR [r9]
	mov QWORD PTR [r9+88], rbp
	mov rbp, r12
	xor rbp, QWORD PTR [r9+24]
	mov QWORD PTR [r9+96], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, rbx
	mov QWORD PTR [r9+104], r12
	mov r12, QWORD PTR [r9+8]
	xor r12, rax
	mov QWORD PTR [r9+112], r13
	mov r13, QWORD PTR [r9+8]
	xor r13, r11
	xor r14, r10
	xor r10, r15
	xor rax, QWORD PTR [r9+24]
	xor rax, QWORD PTR [r9]
	mov r15, rcx
	xor r15, QWORD PTR [r9+32]
	xor rcx, QWORD PTR [r9+40]
	xor rcx, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+80]
	xor r14, QWORD PTR [r9]
	mov QWORD PTR [r9+8], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+32]
	mov QWORD PTR [r9+120], r14
	mov r14, QWORD PTR [r9+16]
	xor r14, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+40]
	mov QWORD PTR [r9+16], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+48]
	mov QWORD PTR [r9+128], r14
	mov r14, QWORD PTR [r9+56]
	xor r14, QWORD PTR [r9+72]
	mov QWORD PTR [r9+56], r14
	mov r14, r11
	xor r14, QWORD PTR [r9+32]
	xor r14, QWORD PTR [r9]
	xor r11, rbp
	xor r11, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+32]
	xor rbp, QWORD PTR [r9+40]
	xor rbp, QWORD PTR [r9]
	xor r12, QWORD PTR [r9+48]
	xor r12, QWORD PTR [r9]
	mov QWORD PTR [r9+40], r11
	mov r11, QWORD PTR [r9+64]
	xor r11, QWORD PTR [r9+112]
	xor r11, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [r9+96]
	xor rax, QWORD PTR [r9+104]
	xor rax, QWORD PTR [r9]
	xor rax, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9]
	mov QWORD PTR [r9+96], rbx
	mov rbx, rcx
	and rbx, r10
	mov QWORD PTR [r9+104], rcx
	mov rcx, rax
	and rcx, r11
	xor rcx, rbx
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [r9+48]
	and rax, r12
	xor rax, rbx
	mov rbx, r15
	and rbx, r14
	mov QWORD PTR [r9+32], r15
	mov r15, QWORD PTR [r9+16]
	and r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+136], r13
	mov r13, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+80]
	xor r13, rbx
	mov rbx, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+128]
	mov QWORD PTR [r9+144], r14
	mov r14, rbp
	and r14, QWORD PTR [r9+64]
	xor r14, rbx
	mov QWORD PTR [r9+152], rbp
	mov rbp, QWORD PTR [r9+8]
	and rbp, QWORD PTR [r9+88]
	xor rbp, rbx
	xor rcx, r14
	xor rax, rbp
	xor r15, r14
	xor r13, rbp
	xor rcx, QWORD PTR [r9+56]
	xor rax, QWORD PTR [r9+120]
	xor r15, QWORD PTR [r9+96]
	xor r13, QWORD PTR [r9+40]
	mov rbp, rcx
	xor rbp, rax
	and rcx, r15
	mov r14, r13
	xor r14, rcx
	mov rbx, rbp
	and rbx, r14
	xor rbx, rax
	mov QWORD PTR [r9+40], r12
	mov r12, r15
	xor r12, r13
	xor rax, rcx
	and rax, r12
	xor rax, r13
	xor r15, rax
	mov r12, r14
	xor r12, rax
	and r13, r12
	xor r15, r13
	xor r14, r13
	and r14, rbx
	xor rbp, r14
	mov r14, rbp
	xor r14, r15
	mov r13, rbx
	xor r13, rax
	mov r12, rbx
	xor r12, rbp
	mov rcx, rax
	xor rcx, r15
	mov QWORD PTR [r9+96], rbx
	mov rbx, r13
	xor rbx, r14
	and r10, rcx
	and r11, r15
	mov QWORD PTR [r9+120], r10
	mov r10, rax
	and r10, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r10
	mov r10, r12
	and r10, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], r10
	mov r10, rbp
	and r10, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], r10
	mov r10, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, r13
	and r10, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r10
	mov r10, rbx
	and r10, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r10
	mov r10, r14
	and r10, QWORD PTR [r9+88]
	and rcx, QWORD PTR [r9+104]
	and r15, QWORD PTR [r9+112]
	and rax, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	and rbp, QWORD PTR [r9+16]
	mov QWORD PTR [r9+16], rbp
	mov rbp, QWORD PTR [r9+96]
	and rbp, QWORD PTR [r9+72]
	and r13, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+152]
	and r14, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], r15
	mov r15, r11
	xor r15, QWORD PTR [r9+64]
	mov QWORD PTR [r9+64], r11
	mov r11, QWORD PTR [r9+144]
	xor r11, QWORD PTR [r9+80]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+128]
	xor rcx, r10
	mov QWORD PTR [r9+152], r10
	mov r10, QWORD PTR [r9+120]
	xor r10, rbx
	xor rax, r15
	mov QWORD PTR [r9+24], r15
	mov r15, r12
	xor r15, r11
	mov QWORD PTR [r9+72], r11
	mov r11, r13
	xor r11, rcx
	xor rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+96], rbp
	mov rbp, QWORD PTR [r9+128]
	xor rbp, r14
	mov QWORD PTR [r9+128], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+144]
	mov QWORD PTR [r9+152], rcx
	mov rcx, QWORD PTR [r9+144]
	xor rcx, QWORD PTR [r9+8]
	mov QWORD PTR [r9+144], rcx
	mov rcx, QWORD PTR [r9+16]
	xor rcx, r15
	xor rbx, r11
	mov QWORD PTR [r9+16], rbx
	mov rbx, r10
	xor rbx, rax
	mov QWORD PTR [r9+32], rbx
	mov rbx, QWORD PTR [r9+120]
	xor rbx, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], rcx
	mov rcx, QWORD PTR [r9+64]
	xor rcx, QWORD PTR [r9+136]
	xor r10, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], r10
	mov r10, QWORD PTR [r9+8]
	xor r10, rbp
	xor r12, rax
	xor r13, QWORD PTR [r9+24]
	xor r14, QWORD PTR [r9+152]
	mov rax, QWORD PTR [r9+72]
	xor rax, QWORD PTR [r9+144]
	xor rbx, QWORD PTR [r9+128]
	xor r15, QWORD PTR [r9+96]
	xor r11, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rbx
	mov rbx, QWORD PTR [r9+96]
	xor rbx, QWORD PTR [r9+152]
	xor rbp, r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+16]
	mov QWORD PTR [r9+152], r13
	mov r13, QWORD PTR [r9+40]
	xor r13, QWORD PTR [r9+32]
	xor rax, QWORD PTR [r9+16]
	xor rax, QWORD PTR [r9]
	xor r10, QWORD PTR [r9+32]
	xor r10, QWORD PTR [r9]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rbx
	xor r12, QWORD PTR [r9]
	xor r14, r13
	xor r14, QWORD PTR [r9]
	xor r15, rbp
	xor r11, rcx
	xor r11, QWORD PTR [r9]
	mov r13, r15
	mov QWORD PTR [r9+80], r12
	mov r12, r11
	mov r11, rax
	mov QWORD PTR [r9+32], r10
	mov r10, QWORD PTR [r9+144]
	mov rbp, QWORD PTR [r9+80]
	mov rcx, QWORD PTR [r9+32]
	mov rbx, r14
	mov rax, QWORD PTR [r9+152]
	mov r15, r13
	mov r14, r13
	xor r14, r12
	and r14, QWORD PTR [r9+408]
	xor r13, r14
	mov r14, r12
	xor r14, r11
	and r14, QWORD PTR [r9+408]
	xor r12, r14
	mov r14, r11
	xor r14, r10
	and r14, QWORD PTR [r9+408]
	xor r11, r14
	mov r14, r10
	xor r14, rbp
	and r14, QWORD PTR [r9+408]
	xor r10, r14
	mov r14, rbp
	xor r14, rcx
	and r14, QWORD PTR [r9+408]
	xor rbp, r14
	mov r14, rcx
	xor r14, rbx
	and r14, QWORD PTR [r9+408]
	xor rcx, r14
	mov r14, rbx
	xor r14, rax
	and r14, QWORD PTR [r9+408]
	xor rbx, r14
	mov r14, rax
	xor r14, r15
	and r14, QWORD PTR [r9+408]
	xor rax, r14
	mov r15, rax
	mov r14, rax
	xor r14, rbx
	and r14, QWORD PTR [r9+416]
	xor rax, r14
	mov r14, rbx
	xor r14, rcx
	and r14, QWORD PTR [r9+416]
	xor rbx, r14
	mov r14, rcx
	xor r14, rbp
	and r14, QWORD PTR [r9+416]
	xor rcx, r14
	mov r14, rbp
	xor r14, r10
	and r14, QWORD PTR [r9+416]
	xor rbp, r14
	mov r14, r10
	xor r14, r11
	and r14, QWORD PTR [r9+416]
	xor r10, r14
	mov r14, r11
	xor r14, r12
	and r14, QWORD PTR [r9+416]
	xor r11, r14
	mov r14, r12
	xor r14, r13
	and r14, QWORD PTR [r9+416]
	xor r12, r14
	mov r14, r13
	xor r14, r15
	and r14, QWORD PTR [r9+416]
	xor r13, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rax
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, rax
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rbx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, rbx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rcx
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rcx
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rbp
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbp
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r10
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, r10
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r11
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, r11
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r12
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r12
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r13
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r13
	ror r14, 40
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	xor rax, QWORD PTR [r9+512]
	mov QWORD PTR [r9+512], rax
	xor rbx, QWORD PTR [r9+520]
	mov QWORD PTR [r9+520], rbx
	xor rcx, QWORD PTR [r9+528]
	mov QWORD PTR [r9+528], rcx
	xor rbp, QWORD PTR [r9+536]
	mov QWORD PTR [r9+536], rbp
	xor r10, QWORD PTR [r9+544]
	mov QWORD PTR [r9+544], r10
	xor r11, QWORD PTR [r9+552]
	mov QWORD PTR [r9+552], r11
	xor r12, QWORD PTR [r9+560]
	mov QWORD PTR [r9+560], r12
	xor r13, QWORD PTR [r9+568]
	mov QWORD PTR [r9+568], r13
	add rsi, 128
	cmp rsi, rdi
	jne 211b
	mov r14, QWORD PTR [r9+2944]
	cmp rsi, r14
	jne 212f
	jmp 213f
212:
	mov rax, QWORD PTR [r9+576]
	mov rbx, QWORD PTR [r9+584]
	mov rcx, QWORD PTR [r9+592]
	mov rbp, QWORD PTR [r9+600]
	mov r10, QWORD PTR [r9+608]
	mov r11, QWORD PTR [r9+616]
	mov r12, QWORD PTR [r9+624]
	mov r13, QWORD PTR [r9+632]
	mov r14, r13
	or r14, QWORD PTR [rsi+120]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r12
	or r14, QWORD PTR [rsi+112]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r11
	or r14, QWORD PTR [rsi+104]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r10
	or r14, QWORD PTR [rsi+96]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, rbp
	or r14, QWORD PTR [rsi+88]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rcx
	or r14, QWORD PTR [rsi+80]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbx
	or r14, QWORD PTR [rsi+72]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rax
	or r14, QWORD PTR [rsi+64]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov r15, r13
	mov r14, r12
	and r14, QWORD PTR [rsi+112]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r11
	and r14, QWORD PTR [rsi+104]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r10
	and r14, QWORD PTR [rsi+96]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, rbp
	and r14, QWORD PTR [rsi+88]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, rcx
	and r14, QWORD PTR [rsi+80]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbx
	and r14, QWORD PTR [rsi+72]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rax
	and r14, QWORD PTR [rsi+64]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, r15
	and r14, QWORD PTR [rsi+120]
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov QWORD PTR [r9+576], rax
	mov QWORD PTR [r9+584], rbx
	mov QWORD PTR [r9+592], rcx
	mov QWORD PTR [r9+600], rbp
	mov QWORD PTR [r9+608], r10
	mov QWORD PTR [r9+616], r11
	mov QWORD PTR [r9+624], r12
	mov QWORD PTR [r9+632], r13
	mov rax, QWORD PTR [r9+512]
	mov rbx, QWORD PTR [r9+520]
	mov rcx, QWORD PTR [r9+528]
	mov rbp, QWORD PTR [r9+536]
	mov r10, QWORD PTR [r9+544]
	mov r11, QWORD PTR [r9+552]
	mov r12, QWORD PTR [r9+560]
	mov r13, QWORD PTR [r9+568]
	mov r15, r13
	mov r14, r12
	and r14, QWORD PTR [rsi+48]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r13, r14
	mov r14, r11
	and r14, QWORD PTR [rsi+40]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r12, r14
	mov r14, r10
	and r14, QWORD PTR [rsi+32]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r11, r14
	mov r14, rbp
	and r14, QWORD PTR [rsi+24]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor r10, r14
	mov r14, rcx
	and r14, QWORD PTR [rsi+16]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbp, r14
	mov r14, rbx
	and r14, QWORD PTR [rsi+8]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rcx, r14
	mov r14, rax
	and r14, QWORD PTR [rsi]
	ror r14, 56
	and r14, QWORD PTR [r9+392]
	xor rbx, r14
	mov r14, r15
	and r14, QWORD PTR [rsi+56]
	ror r14, 8
	and r14, QWORD PTR [r9+392]
	xor rax, r14
	mov r14, r13
	or r14, QWORD PTR [rsi+56]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r13, r14
	mov r14, r12
	or r14, QWORD PTR [rsi+48]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r12, r14
	mov r14, r11
	or r14, QWORD PTR [rsi+40]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r11, r14
	mov r14, r10
	or r14, QWORD PTR [rsi+32]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor r10, r14
	mov r14, rbp
	or r14, QWORD PTR [rsi+24]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbp, r14
	mov r14, rcx
	or r14, QWORD PTR [rsi+16]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rcx, r14
	mov r14, rbx
	or r14, QWORD PTR [rsi+8]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rbx, r14
	mov r14, rax
	or r14, QWORD PTR [rsi]
	ror r14, 8
	and r14, QWORD PTR [r9+384]
	xor rax, r14
	mov QWORD PTR [r9+512], rax
	mov QWORD PTR [r9+520], rbx
	mov QWORD PTR [r9+528], rcx
	mov QWORD PTR [r9+536], rbp
	mov QWORD PTR [r9+544], r10
	mov QWORD PTR [r9+552], r11
	mov QWORD PTR [r9+560], r12
	mov QWORD PTR [r9+568], r13
	add rsi, 128
213:
	mov r14, QWORD PTR [r9+2944]
	cmp rsi, r14
	jne 210b
	xor rax, QWORD PTR [rsi+64]
	xor rbx, QWORD PTR [rsi+72]
	xor rcx, QWORD PTR [rsi+80]
	xor rbp, QWORD PTR [rsi+88]
	xor r10, QWORD PTR [rsi+96]
	xor r11, QWORD PTR [rsi+104]
	xor r12, QWORD PTR [rsi+112]
	xor r13, QWORD PTR [rsi+120]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rdx+8], rax
	mov QWORD PTR [rdx+24], rbx
	mov QWORD PTR [rdx+40], rcx
	mov QWORD PTR [rdx+56], rbp
	mov QWORD PTR [rdx+72], r10
	mov QWORD PTR [rdx+88], r11
	mov QWORD PTR [rdx+104], r12
	mov QWORD PTR [rdx+120], r13
	mov rax, QWORD PTR [r9+576]
	mov rbx, QWORD PTR [r9+584]
	mov rcx, QWORD PTR [r9+592]
	mov rbp, QWORD PTR [r9+600]
	mov r10, QWORD PTR [r9+608]
	mov r11, QWORD PTR [r9+616]
	mov r12, QWORD PTR [r9+624]
	mov r13, QWORD PTR [r9+632]
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+16], rbx
	mov QWORD PTR [rdx+32], rcx
	mov QWORD PTR [rdx+48], rbp
	mov QWORD PTR [rdx+64], r10
	mov QWORD PTR [rdx+80], r11
	mov QWORD PTR [rdx+96], r12
	mov QWORD PTR [rdx+112], r13
	mov rdx, QWORD PTR [r9+2952]
	mov r8, QWORD PTR [r9+2960]
	mov rdi, QWORD PTR [r9+2944]
	movabs rcx, 8
	cmp r8, 8
	jb 214f
	jmp 215f
214:
	mov rcx, r8
215:
	mov rax, r9
	add rax, 3016
	mov rbx, rdx
216:
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	mov rbp, QWORD PTR [rax+8]
	mov QWORD PTR [rbx+8], rbp
	add rax, 16
	add rbx, 16
	sub rcx, 1
	jne 216b
	cmp r8, 8
	jb 217f
	add rdx, 128
	sub r8, 8
	jmp 218f
217:
	sub r8, r8
218:
	jne 26b
	jmp 25f
24:
25:
	mov rbx, QWORD PTR [r9+2968]
	mov rbp, QWORD PTR [r9+2976]
	mov r12, QWORD PTR [r9+2984]
	mov r13, QWORD PTR [r9+2992]
	mov r14, QWORD PTR [r9+3000]
	mov r15, QWORD PTR [r9+3008]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	mov QWORD PTR [rsp+3208], r11
	lea rsp, [rsp+3216]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	lea rsp, [rsp-3208]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3208]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6
