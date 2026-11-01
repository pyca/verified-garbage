// The functions of `src/md5.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_compress:
	test rdx, rdx
	je 20f
	mov eax, DWORD PTR [rdi]
	mov r8d, DWORD PTR [rdi+4]
	mov r9d, DWORD PTR [rdi+8]
	mov r10d, DWORD PTR [rdi+12]
22:
	add eax, DWORD PTR [rsi]
	add eax, -680876936
	mov r11d, r9d
	xor r11d, r10d
	and r11d, r8d
	xor r11d, r10d
	add eax, r11d
	ror eax, 25
	add eax, r8d
	add r10d, DWORD PTR [rsi+4]
	add r10d, -389564586
	mov r11d, r8d
	xor r11d, r9d
	and r11d, eax
	xor r11d, r9d
	add r10d, r11d
	ror r10d, 20
	add r10d, eax
	add r9d, DWORD PTR [rsi+8]
	add r9d, 606105819
	mov r11d, eax
	xor r11d, r8d
	and r11d, r10d
	xor r11d, r8d
	add r9d, r11d
	ror r9d, 15
	add r9d, r10d
	add r8d, DWORD PTR [rsi+12]
	add r8d, -1044525330
	mov r11d, r10d
	xor r11d, eax
	and r11d, r9d
	xor r11d, eax
	add r8d, r11d
	ror r8d, 10
	add r8d, r9d
	add eax, DWORD PTR [rsi+16]
	add eax, -176418897
	mov r11d, r9d
	xor r11d, r10d
	and r11d, r8d
	xor r11d, r10d
	add eax, r11d
	ror eax, 25
	add eax, r8d
	add r10d, DWORD PTR [rsi+20]
	add r10d, 1200080426
	mov r11d, r8d
	xor r11d, r9d
	and r11d, eax
	xor r11d, r9d
	add r10d, r11d
	ror r10d, 20
	add r10d, eax
	add r9d, DWORD PTR [rsi+24]
	add r9d, -1473231341
	mov r11d, eax
	xor r11d, r8d
	and r11d, r10d
	xor r11d, r8d
	add r9d, r11d
	ror r9d, 15
	add r9d, r10d
	add r8d, DWORD PTR [rsi+28]
	add r8d, -45705983
	mov r11d, r10d
	xor r11d, eax
	and r11d, r9d
	xor r11d, eax
	add r8d, r11d
	ror r8d, 10
	add r8d, r9d
	add eax, DWORD PTR [rsi+32]
	add eax, 1770035416
	mov r11d, r9d
	xor r11d, r10d
	and r11d, r8d
	xor r11d, r10d
	add eax, r11d
	ror eax, 25
	add eax, r8d
	add r10d, DWORD PTR [rsi+36]
	add r10d, -1958414417
	mov r11d, r8d
	xor r11d, r9d
	and r11d, eax
	xor r11d, r9d
	add r10d, r11d
	ror r10d, 20
	add r10d, eax
	add r9d, DWORD PTR [rsi+40]
	add r9d, -42063
	mov r11d, eax
	xor r11d, r8d
	and r11d, r10d
	xor r11d, r8d
	add r9d, r11d
	ror r9d, 15
	add r9d, r10d
	add r8d, DWORD PTR [rsi+44]
	add r8d, -1990404162
	mov r11d, r10d
	xor r11d, eax
	and r11d, r9d
	xor r11d, eax
	add r8d, r11d
	ror r8d, 10
	add r8d, r9d
	add eax, DWORD PTR [rsi+48]
	add eax, 1804603682
	mov r11d, r9d
	xor r11d, r10d
	and r11d, r8d
	xor r11d, r10d
	add eax, r11d
	ror eax, 25
	add eax, r8d
	add r10d, DWORD PTR [rsi+52]
	add r10d, -40341101
	mov r11d, r8d
	xor r11d, r9d
	and r11d, eax
	xor r11d, r9d
	add r10d, r11d
	ror r10d, 20
	add r10d, eax
	add r9d, DWORD PTR [rsi+56]
	add r9d, -1502002290
	mov r11d, eax
	xor r11d, r8d
	and r11d, r10d
	xor r11d, r8d
	add r9d, r11d
	ror r9d, 15
	add r9d, r10d
	add r8d, DWORD PTR [rsi+60]
	add r8d, 1236535329
	mov r11d, r10d
	xor r11d, eax
	and r11d, r9d
	xor r11d, eax
	add r8d, r11d
	ror r8d, 10
	add r8d, r9d
	add eax, DWORD PTR [rsi+4]
	add eax, -165796510
	mov r11d, r10d
	xor r11d, -1
	and r11d, r9d
	add eax, r11d
	mov r11d, r10d
	and r11d, r8d
	add eax, r11d
	ror eax, 27
	add eax, r8d
	add r10d, DWORD PTR [rsi+24]
	add r10d, -1069501632
	mov r11d, r9d
	xor r11d, -1
	and r11d, r8d
	add r10d, r11d
	mov r11d, r9d
	and r11d, eax
	add r10d, r11d
	ror r10d, 23
	add r10d, eax
	add r9d, DWORD PTR [rsi+44]
	add r9d, 643717713
	mov r11d, r8d
	xor r11d, -1
	and r11d, eax
	add r9d, r11d
	mov r11d, r8d
	and r11d, r10d
	add r9d, r11d
	ror r9d, 18
	add r9d, r10d
	add r8d, DWORD PTR [rsi]
	add r8d, -373897302
	mov r11d, eax
	xor r11d, -1
	and r11d, r10d
	add r8d, r11d
	mov r11d, eax
	and r11d, r9d
	add r8d, r11d
	ror r8d, 12
	add r8d, r9d
	add eax, DWORD PTR [rsi+20]
	add eax, -701558691
	mov r11d, r10d
	xor r11d, -1
	and r11d, r9d
	add eax, r11d
	mov r11d, r10d
	and r11d, r8d
	add eax, r11d
	ror eax, 27
	add eax, r8d
	add r10d, DWORD PTR [rsi+40]
	add r10d, 38016083
	mov r11d, r9d
	xor r11d, -1
	and r11d, r8d
	add r10d, r11d
	mov r11d, r9d
	and r11d, eax
	add r10d, r11d
	ror r10d, 23
	add r10d, eax
	add r9d, DWORD PTR [rsi+60]
	add r9d, -660478335
	mov r11d, r8d
	xor r11d, -1
	and r11d, eax
	add r9d, r11d
	mov r11d, r8d
	and r11d, r10d
	add r9d, r11d
	ror r9d, 18
	add r9d, r10d
	add r8d, DWORD PTR [rsi+16]
	add r8d, -405537848
	mov r11d, eax
	xor r11d, -1
	and r11d, r10d
	add r8d, r11d
	mov r11d, eax
	and r11d, r9d
	add r8d, r11d
	ror r8d, 12
	add r8d, r9d
	add eax, DWORD PTR [rsi+36]
	add eax, 568446438
	mov r11d, r10d
	xor r11d, -1
	and r11d, r9d
	add eax, r11d
	mov r11d, r10d
	and r11d, r8d
	add eax, r11d
	ror eax, 27
	add eax, r8d
	add r10d, DWORD PTR [rsi+56]
	add r10d, -1019803690
	mov r11d, r9d
	xor r11d, -1
	and r11d, r8d
	add r10d, r11d
	mov r11d, r9d
	and r11d, eax
	add r10d, r11d
	ror r10d, 23
	add r10d, eax
	add r9d, DWORD PTR [rsi+12]
	add r9d, -187363961
	mov r11d, r8d
	xor r11d, -1
	and r11d, eax
	add r9d, r11d
	mov r11d, r8d
	and r11d, r10d
	add r9d, r11d
	ror r9d, 18
	add r9d, r10d
	add r8d, DWORD PTR [rsi+32]
	add r8d, 1163531501
	mov r11d, eax
	xor r11d, -1
	and r11d, r10d
	add r8d, r11d
	mov r11d, eax
	and r11d, r9d
	add r8d, r11d
	ror r8d, 12
	add r8d, r9d
	add eax, DWORD PTR [rsi+52]
	add eax, -1444681467
	mov r11d, r10d
	xor r11d, -1
	and r11d, r9d
	add eax, r11d
	mov r11d, r10d
	and r11d, r8d
	add eax, r11d
	ror eax, 27
	add eax, r8d
	add r10d, DWORD PTR [rsi+8]
	add r10d, -51403784
	mov r11d, r9d
	xor r11d, -1
	and r11d, r8d
	add r10d, r11d
	mov r11d, r9d
	and r11d, eax
	add r10d, r11d
	ror r10d, 23
	add r10d, eax
	add r9d, DWORD PTR [rsi+28]
	add r9d, 1735328473
	mov r11d, r8d
	xor r11d, -1
	and r11d, eax
	add r9d, r11d
	mov r11d, r8d
	and r11d, r10d
	add r9d, r11d
	ror r9d, 18
	add r9d, r10d
	add r8d, DWORD PTR [rsi+48]
	add r8d, -1926607734
	mov r11d, eax
	xor r11d, -1
	and r11d, r10d
	add r8d, r11d
	mov r11d, eax
	and r11d, r9d
	add r8d, r11d
	ror r8d, 12
	add r8d, r9d
	add eax, DWORD PTR [rsi+20]
	add eax, -378558
	mov r11d, r9d
	xor r11d, r10d
	xor r11d, r8d
	add eax, r11d
	ror eax, 28
	add eax, r8d
	add r10d, DWORD PTR [rsi+32]
	add r10d, -2022574463
	mov r11d, r8d
	xor r11d, r9d
	xor r11d, eax
	add r10d, r11d
	ror r10d, 21
	add r10d, eax
	add r9d, DWORD PTR [rsi+44]
	add r9d, 1839030562
	mov r11d, eax
	xor r11d, r8d
	xor r11d, r10d
	add r9d, r11d
	ror r9d, 16
	add r9d, r10d
	add r8d, DWORD PTR [rsi+56]
	add r8d, -35309556
	mov r11d, r10d
	xor r11d, eax
	xor r11d, r9d
	add r8d, r11d
	ror r8d, 9
	add r8d, r9d
	add eax, DWORD PTR [rsi+4]
	add eax, -1530992060
	mov r11d, r9d
	xor r11d, r10d
	xor r11d, r8d
	add eax, r11d
	ror eax, 28
	add eax, r8d
	add r10d, DWORD PTR [rsi+16]
	add r10d, 1272893353
	mov r11d, r8d
	xor r11d, r9d
	xor r11d, eax
	add r10d, r11d
	ror r10d, 21
	add r10d, eax
	add r9d, DWORD PTR [rsi+28]
	add r9d, -155497632
	mov r11d, eax
	xor r11d, r8d
	xor r11d, r10d
	add r9d, r11d
	ror r9d, 16
	add r9d, r10d
	add r8d, DWORD PTR [rsi+40]
	add r8d, -1094730640
	mov r11d, r10d
	xor r11d, eax
	xor r11d, r9d
	add r8d, r11d
	ror r8d, 9
	add r8d, r9d
	add eax, DWORD PTR [rsi+52]
	add eax, 681279174
	mov r11d, r9d
	xor r11d, r10d
	xor r11d, r8d
	add eax, r11d
	ror eax, 28
	add eax, r8d
	add r10d, DWORD PTR [rsi]
	add r10d, -358537222
	mov r11d, r8d
	xor r11d, r9d
	xor r11d, eax
	add r10d, r11d
	ror r10d, 21
	add r10d, eax
	add r9d, DWORD PTR [rsi+12]
	add r9d, -722521979
	mov r11d, eax
	xor r11d, r8d
	xor r11d, r10d
	add r9d, r11d
	ror r9d, 16
	add r9d, r10d
	add r8d, DWORD PTR [rsi+24]
	add r8d, 76029189
	mov r11d, r10d
	xor r11d, eax
	xor r11d, r9d
	add r8d, r11d
	ror r8d, 9
	add r8d, r9d
	add eax, DWORD PTR [rsi+36]
	add eax, -640364487
	mov r11d, r9d
	xor r11d, r10d
	xor r11d, r8d
	add eax, r11d
	ror eax, 28
	add eax, r8d
	add r10d, DWORD PTR [rsi+48]
	add r10d, -421815835
	mov r11d, r8d
	xor r11d, r9d
	xor r11d, eax
	add r10d, r11d
	ror r10d, 21
	add r10d, eax
	add r9d, DWORD PTR [rsi+60]
	add r9d, 530742520
	mov r11d, eax
	xor r11d, r8d
	xor r11d, r10d
	add r9d, r11d
	ror r9d, 16
	add r9d, r10d
	add r8d, DWORD PTR [rsi+8]
	add r8d, -995338651
	mov r11d, r10d
	xor r11d, eax
	xor r11d, r9d
	add r8d, r11d
	ror r8d, 9
	add r8d, r9d
	add eax, DWORD PTR [rsi]
	add eax, -198630844
	mov r11d, r10d
	xor r11d, -1
	or r11d, r8d
	xor r11d, r9d
	add eax, r11d
	ror eax, 26
	add eax, r8d
	add r10d, DWORD PTR [rsi+28]
	add r10d, 1126891415
	mov r11d, r9d
	xor r11d, -1
	or r11d, eax
	xor r11d, r8d
	add r10d, r11d
	ror r10d, 22
	add r10d, eax
	add r9d, DWORD PTR [rsi+56]
	add r9d, -1416354905
	mov r11d, r8d
	xor r11d, -1
	or r11d, r10d
	xor r11d, eax
	add r9d, r11d
	ror r9d, 17
	add r9d, r10d
	add r8d, DWORD PTR [rsi+20]
	add r8d, -57434055
	mov r11d, eax
	xor r11d, -1
	or r11d, r9d
	xor r11d, r10d
	add r8d, r11d
	ror r8d, 11
	add r8d, r9d
	add eax, DWORD PTR [rsi+48]
	add eax, 1700485571
	mov r11d, r10d
	xor r11d, -1
	or r11d, r8d
	xor r11d, r9d
	add eax, r11d
	ror eax, 26
	add eax, r8d
	add r10d, DWORD PTR [rsi+12]
	add r10d, -1894986606
	mov r11d, r9d
	xor r11d, -1
	or r11d, eax
	xor r11d, r8d
	add r10d, r11d
	ror r10d, 22
	add r10d, eax
	add r9d, DWORD PTR [rsi+40]
	add r9d, -1051523
	mov r11d, r8d
	xor r11d, -1
	or r11d, r10d
	xor r11d, eax
	add r9d, r11d
	ror r9d, 17
	add r9d, r10d
	add r8d, DWORD PTR [rsi+4]
	add r8d, -2054922799
	mov r11d, eax
	xor r11d, -1
	or r11d, r9d
	xor r11d, r10d
	add r8d, r11d
	ror r8d, 11
	add r8d, r9d
	add eax, DWORD PTR [rsi+32]
	add eax, 1873313359
	mov r11d, r10d
	xor r11d, -1
	or r11d, r8d
	xor r11d, r9d
	add eax, r11d
	ror eax, 26
	add eax, r8d
	add r10d, DWORD PTR [rsi+60]
	add r10d, -30611744
	mov r11d, r9d
	xor r11d, -1
	or r11d, eax
	xor r11d, r8d
	add r10d, r11d
	ror r10d, 22
	add r10d, eax
	add r9d, DWORD PTR [rsi+24]
	add r9d, -1560198380
	mov r11d, r8d
	xor r11d, -1
	or r11d, r10d
	xor r11d, eax
	add r9d, r11d
	ror r9d, 17
	add r9d, r10d
	add r8d, DWORD PTR [rsi+52]
	add r8d, 1309151649
	mov r11d, eax
	xor r11d, -1
	or r11d, r9d
	xor r11d, r10d
	add r8d, r11d
	ror r8d, 11
	add r8d, r9d
	add eax, DWORD PTR [rsi+16]
	add eax, -145523070
	mov r11d, r10d
	xor r11d, -1
	or r11d, r8d
	xor r11d, r9d
	add eax, r11d
	ror eax, 26
	add eax, r8d
	add r10d, DWORD PTR [rsi+44]
	add r10d, -1120210379
	mov r11d, r9d
	xor r11d, -1
	or r11d, eax
	xor r11d, r8d
	add r10d, r11d
	ror r10d, 22
	add r10d, eax
	add r9d, DWORD PTR [rsi+8]
	add r9d, 718787259
	mov r11d, r8d
	xor r11d, -1
	or r11d, r10d
	xor r11d, eax
	add r9d, r11d
	ror r9d, 17
	add r9d, r10d
	add r8d, DWORD PTR [rsi+36]
	add r8d, -343485551
	mov r11d, eax
	xor r11d, -1
	or r11d, r9d
	xor r11d, r10d
	add r8d, r11d
	ror r8d, 11
	add r8d, r9d
	add eax, DWORD PTR [rdi]
	add r8d, DWORD PTR [rdi+4]
	add r9d, DWORD PTR [rdi+8]
	add r10d, DWORD PTR [rdi+12]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], r8d
	mov DWORD PTR [rdi+8], r9d
	mov DWORD PTR [rdi+12], r10d
	add rsi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	ret
	.p2align 6

vg_md5_init:
	mov eax, 1732584193
	mov DWORD PTR [rdi], eax
	mov eax, -271733879
	mov DWORD PTR [rdi+4], eax
	mov eax, -1732584194
	mov DWORD PTR [rdi+8], eax
	mov eax, 271733878
	mov DWORD PTR [rdi+12], eax
	ret
	.p2align 6

vg_md5_update:
	lea rsp, [rsp-120]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+64], rbx
	mov QWORD PTR [r8+72], rbp
	mov QWORD PTR [r8+80], r12
	mov QWORD PTR [r8+88], r13
	mov QWORD PTR [r8+96], r14
	mov QWORD PTR [r8+104], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+16], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+16], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 16
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+16], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+16], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 16
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+64]
	mov rbp, QWORD PTR [r15+72]
	mov r12, QWORD PTR [r15+80]
	mov r13, QWORD PTR [r15+88]
	mov r14, QWORD PTR [r15+96]
	mov r15, QWORD PTR [r15+104]
	lea rsp, [rsp+120]
	ret
	.p2align 6

vg_md5_finalize:
	lea rsp, [rsp-120]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+64], rbx
	mov QWORD PTR [rcx+72], rbp
	mov QWORD PTR [rcx+80], r12
	mov QWORD PTR [rcx+88], r13
	mov QWORD PTR [rcx+96], r14
	mov QWORD PTR [rcx+104], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+16], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+16], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+16], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rbx+72], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+16], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+64], xmm0
24:
	mov rsi, rbx
	add rsi, 16
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov eax, DWORD PTR [rbx]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	mov DWORD PTR [rbp+12], eax
	mov rbx, QWORD PTR [r15+64]
	mov rbp, QWORD PTR [r15+72]
	mov r12, QWORD PTR [r15+80]
	mov r13, QWORD PTR [r15+88]
	mov r14, QWORD PTR [r15+96]
	mov r15, QWORD PTR [r15+104]
	lea rsp, [rsp+120]
	ret
	.p2align 6

vg_md5_update_scratch:
	mov QWORD PTR [r8+64], rbx
	mov QWORD PTR [r8+72], rbp
	mov QWORD PTR [r8+80], r12
	mov QWORD PTR [r8+88], r13
	mov QWORD PTR [r8+96], r14
	mov QWORD PTR [r8+104], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+16], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+16], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 16
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+16], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+16], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 16
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+64]
	mov rbp, QWORD PTR [r15+72]
	mov r12, QWORD PTR [r15+80]
	mov r13, QWORD PTR [r15+88]
	mov r14, QWORD PTR [r15+96]
	mov r15, QWORD PTR [r15+104]
	ret
	.p2align 6

vg_md5_finalize_scratch:
	mov QWORD PTR [rcx+64], rbx
	mov QWORD PTR [rcx+72], rbp
	mov QWORD PTR [rcx+80], r12
	mov QWORD PTR [rcx+88], r13
	mov QWORD PTR [rcx+96], r14
	mov QWORD PTR [rcx+104], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+16], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+16], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+16], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rbx+72], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+16], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+64], xmm0
24:
	mov rsi, rbx
	add rsi, 16
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov eax, DWORD PTR [rbx]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	mov DWORD PTR [rbp+12], eax
	mov rbx, QWORD PTR [r15+64]
	mov rbp, QWORD PTR [r15+72]
	mov r12, QWORD PTR [r15+80]
	mov r13, QWORD PTR [r15+88]
	mov r14, QWORD PTR [r15+96]
	mov r15, QWORD PTR [r15+104]
	ret
	.p2align 6
