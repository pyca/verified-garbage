// The functions of `src/internal/vg_chacha20_poly1305_seal_split_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_split_avx512:
	lea rsp, [rsp-1736]
	mov rax, QWORD PTR [rsp+1744]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+1752]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+1760]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax], rdi
	mov QWORD PTR [rax+8], rsi
	mov QWORD PTR [rax+16], rcx
	mov QWORD PTR [rax+24], r8
	mov r10, QWORD PTR [rsp+16]
	mov rcx, r10
	and rcx, 1023
	add rcx, 63
	and rcx, -64
	mov edi, 0
	cmp rcx, 961
	cmovae rcx, rdi
	cmp r10, 961
	cmovb rcx, r10
	cmp r9, rcx
	cmovb rcx, r9
	mov rsi, r8
	mov rdi, QWORD PTR [rsp+8]
	cmp rcx, 128
	jb 20f
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 ZMMWORD PTR [rdi], zmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 63
	mov r8, rcx
	sub r8, 128
	cmp r8, r10
	jb 22f
24:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+r10*1+64]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+r10*1+64], zmm1
	add r10, 128
	cmp r8, r10
	jae 24b
	jmp 23f
22:
23:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+rcx*1-128]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1-64]
	vmovdqu32 ZMMWORD PTR [rdi+rcx*1-128], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+rcx*1-64], zmm1
	jmp 21f
20:
	cmp rcx, 64
	jb 25f
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1-64]
	vmovdqu32 ZMMWORD PTR [rdi], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+rcx*1-64], zmm1
	jmp 26f
25:
	cmp rcx, 32
	jb 27f
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1-32]
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+rcx*1-32], ymm1
	jmp 28f
27:
	cmp rcx, 16
	jb 29f
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	vmovdqu XMMWORD PTR [rdi], xmm0
	vmovdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 210f
29:
	cmp rcx, 8
	jb 211f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 212f
211:
	cmp rcx, 4
	jb 213f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 214f
213:
	mov r10d, 0
	cmp r10, rcx
	je 215f
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	jmp 216f
215:
216:
214:
212:
210:
28:
26:
21:
	vzeroupper
	mov rax, QWORD PTR [rsp+32]
	mov rdi, QWORD PTR [rax]
	mov rsi, QWORD PTR [rax+8]
	mov rcx, QWORD PTR [rax+16]
	mov r8, QWORD PTR [rax+24]
	mov r10, QWORD PTR [rsp+32]
	mov r11, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [rsp+8]
	push r9
	push r8
	push r10
	push r11
	push rax
	mov r8, rax
	mov r9, QWORD PTR [rsp+56]
	mov rax, QWORD PTR [rsp+16]
	mov r11, QWORD PTR [rsp+8]
	mov QWORD PTR [rax], rbx
	mov QWORD PTR [rax+8], rbp
	mov QWORD PTR [rax+16], r13
	mov QWORD PTR [rax+24], r14
	mov QWORD PTR [rax+32], r15
	mov QWORD PTR [rax+40], r12
	mov r15, rax
	mov r12, r11
	mov rbx, rdx
	mov rbp, rcx
	mov r14, r8
	mov r13, r9
	movabs rax, 3684054920433006693
	mov QWORD PTR [r15+64], rax
	movabs rax, 7719281312240119090
	mov QWORD PTR [r15+72], rax
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r15+80], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r15+88], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r15+104], rax
	mov eax, DWORD PTR [rsi]
	shl rax, 32
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [rsi+4]
	mov QWORD PTR [r15+120], rax
	movabs rax, 3684054920433006693
	mov QWORD PTR [r15+608], rax
	movabs rax, 7719281312240119090
	mov QWORD PTR [r15+616], rax
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r15+624], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r15+632], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r15+640], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r15+648], rax
	mov eax, DWORD PTR [rsi]
	shl rax, 32
	mov QWORD PTR [r15+656], rax
	mov rax, QWORD PTR [rsi+4]
	mov QWORD PTR [r15+664], rax
	mov edx, 0
	cmp r13, 961
	jb 218f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 220f
	mov edx, 0
	jmp 221f
220:
221:
	jmp 219f
218:
	mov rdx, r13
219:
	add rdx, 64
	vpxord zmm0, zmm0, zmm0
	mov ecx, 0
222:
	vmovdqu32 ZMMWORD PTR [r15+rcx*1+672], zmm0
	add rcx, 64
	cmp rcx, rdx
	jb 222b
	vzeroupper
	mov rdi, r15
	add rdi, 608
	mov rsi, r15
	add rsi, 672
	mov rcx, r15
	add rcx, 128
	call {vg_chacha20_xor_avx512}
	mov r15, rsi
	sub r15, 128
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 672
	call {vg_poly1305_init}
	mov r15, rdi
	sub r15, 448
	mov rdi, r15
	add rdi, 448
	mov rsi, rbx
	mov rdx, rbp
	shr rdx, 4
	je 223f
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 224f
223:
224:
	mov rdx, rbp
	and rdx, 15
	jne 225f
	je 227f
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	add rax, 1
	add rax, 1
	jmp 228f
227:
228:
226:
	mov QWORD PTR [r15+592], rbp
	mov QWORD PTR [r15+600], r13
	cmp r13, 961
	jb 237f
	mov edx, 0
	cmp r13, 961
	jb 239f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 241f
	mov edx, 0
	jmp 242f
241:
242:
	jmp 240f
239:
	mov rdx, r13
240:
	test rdx, rdx
	je 243f
	mov rsi, r15
	add rsi, 736
	mov ecx, 0
	mov rax, rdx
	shr rax, 6
	je 245f
247:
	vmovdqu32 zmm0, ZMMWORD PTR [r14+rcx*1]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [r14+rcx*1], zmm0
	add rcx, 64
	sub rax, 1
	jne 247b
	jmp 246f
245:
246:
	mov rdi, r14
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 248f
250:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 250b
	jmp 249f
248:
249:
	cmp rcx, rdx
	je 251f
253:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 253b
	jmp 252f
251:
252:
	jmp 244f
243:
244:
	mov edx, 0
	cmp r13, 961
	jb 254f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 256f
	mov edx, 0
	jmp 257f
256:
257:
	jmp 255f
254:
	mov rdx, r13
255:
	mov rax, rdx
	shr rax, 6
	add rax, 1
	mov DWORD PTR [r15+112], eax
	mov rsi, r14
	add rsi, rdx
	mov rax, r13
	sub rax, rdx
	mov rdx, rax
	mov rdi, r15
	add rdi, 64
	mov rcx, r15
	add rcx, 128
	mov r8, rdx
	mov r9, rcx
	mov rcx, rsi
	mov rax, rsi
	sub rax, r14
	mov rdx, QWORD PTR [rsp+32]
	cmp rdx, rax
	cmovb rax, rdx
	mov rsi, QWORD PTR [rsp+24]
	add rsi, rax
	sub rdx, rax
	mov rax, r8
	shr rax, 10
	shl rax, 10
	mov r10, rdx
	shr r10, 6
	shl r10, 6
	mov r11, r8
	sub r11, rax
	cmp r11, 513
	jb 258f
	jmp 259f
258:
	cmp r10, rax
	cmovae r10, rax
259:
	mov QWORD PTR [r9], rbx
	mov rbx, r8
	mov r11, rdi
	mov rdi, rcx
	add rdi, r10
	add rsi, r10
	mov rcx, rdx
	sub rcx, r10
	mov rdx, r10
	cmp rcx, 128
	jb 260f
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 ZMMWORD PTR [rdi], zmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 63
	mov r8, rcx
	sub r8, 128
	cmp r8, r10
	jb 262f
264:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+r10*1+64]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+r10*1+64], zmm1
	add r10, 128
	cmp r8, r10
	jae 264b
	jmp 263f
262:
263:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+rcx*1-128]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1-64]
	vmovdqu32 ZMMWORD PTR [rdi+rcx*1-128], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+rcx*1-64], zmm1
	jmp 261f
260:
	cmp rcx, 64
	jb 265f
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1-64]
	vmovdqu32 ZMMWORD PTR [rdi], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+rcx*1-64], zmm1
	jmp 266f
265:
	cmp rcx, 32
	jb 267f
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1-32]
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+rcx*1-32], ymm1
	jmp 268f
267:
	cmp rcx, 16
	jb 269f
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	vmovdqu XMMWORD PTR [rdi], xmm0
	vmovdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 270f
269:
	cmp rcx, 8
	jb 271f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 272f
271:
	cmp rcx, 4
	jb 273f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 274f
273:
	mov r10d, 0
	cmp r10, rcx
	je 275f
277:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 277b
	jmp 276f
275:
276:
274:
272:
270:
268:
266:
261:
	vzeroupper
	mov rax, QWORD PTR [r9]
	mov r8, rsi
	sub r8, rdx
	mov rsi, rdi
	sub rsi, rdx
	mov r10, rdx
	mov rdx, rbx
	mov rbx, rax
	mov rdi, r11
	mov rcx, r9
	movabs rax, 0
	mov QWORD PTR [rcx+256], rax
	movabs rax, 0
	mov QWORD PTR [rcx+264], rax
	movabs rax, 1
	mov QWORD PTR [rcx+272], rax
	movabs rax, 0
	mov QWORD PTR [rcx+280], rax
	movabs rax, 2
	mov QWORD PTR [rcx+288], rax
	movabs rax, 0
	mov QWORD PTR [rcx+296], rax
	movabs rax, 3
	mov QWORD PTR [rcx+304], rax
	movabs rax, 0
	mov QWORD PTR [rcx+312], rax
	movabs rax, 4
	mov QWORD PTR [rcx+192], rax
	movabs rax, 0
	mov QWORD PTR [rcx+200], rax
	movabs rax, 5
	mov QWORD PTR [rcx+208], rax
	movabs rax, 0
	mov QWORD PTR [rcx+216], rax
	movabs rax, 6
	mov QWORD PTR [rcx+224], rax
	movabs rax, 0
	mov QWORD PTR [rcx+232], rax
	movabs rax, 7
	mov QWORD PTR [rcx+240], rax
	movabs rax, 0
	mov QWORD PTR [rcx+248], rax
	movabs rax, 4294967296
	mov QWORD PTR [rcx+128], rax
	movabs rax, 12884901890
	mov QWORD PTR [rcx+136], rax
	movabs rax, 21474836484
	mov QWORD PTR [rcx+144], rax
	movabs rax, 30064771078
	mov QWORD PTR [rcx+152], rax
	movabs rax, 38654705672
	mov QWORD PTR [rcx+160], rax
	movabs rax, 47244640266
	mov QWORD PTR [rcx+168], rax
	movabs rax, 55834574860
	mov QWORD PTR [rcx+176], rax
	movabs rax, 64424509454
	mov QWORD PTR [rcx+184], rax
	cmp rdx, 1024
	jb 278f
280:
	vpbroadcastd zmm12, DWORD PTR [rdi+48]
	vpbroadcastd zmm13, DWORD PTR [rdi+52]
	vpbroadcastd zmm14, DWORD PTR [rdi+56]
	vpbroadcastd zmm15, DWORD PTR [rdi+60]
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+128]
	vpaddd zmm12, zmm12, zmm0
	vpbroadcastd zmm0, DWORD PTR [rdi]
	vpbroadcastd zmm1, DWORD PTR [rdi+4]
	vpbroadcastd zmm2, DWORD PTR [rdi+8]
	vpbroadcastd zmm3, DWORD PTR [rdi+12]
	vpbroadcastd zmm4, DWORD PTR [rdi+16]
	vpbroadcastd zmm5, DWORD PTR [rdi+20]
	vpbroadcastd zmm6, DWORD PTR [rdi+24]
	vpbroadcastd zmm7, DWORD PTR [rdi+28]
	vpbroadcastd zmm8, DWORD PTR [rdi+32]
	vpbroadcastd zmm9, DWORD PTR [rdi+36]
	vpbroadcastd zmm10, DWORD PTR [rdi+40]
	vpbroadcastd zmm11, DWORD PTR [rdi+44]
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vmovdqu32 ZMMWORD PTR [rcx], zmm14
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm15
	vpaddd zmm0, zmm0, DWORD PTR [rdi]{1to16}
	vpaddd zmm1, zmm1, DWORD PTR [rdi+4]{1to16}
	vpaddd zmm2, zmm2, DWORD PTR [rdi+8]{1to16}
	vpaddd zmm3, zmm3, DWORD PTR [rdi+12]{1to16}
	vpunpckldq zmm14, zmm0, zmm1
	vpunpckhdq zmm1, zmm0, zmm1
	vpunpckldq zmm15, zmm2, zmm3
	vpunpckhdq zmm3, zmm2, zmm3
	vpunpcklqdq zmm0, zmm14, zmm15
	vpunpckhqdq zmm14, zmm14, zmm15
	vpunpcklqdq zmm2, zmm1, zmm3
	vpunpckhqdq zmm3, zmm1, zmm3
	vpaddd zmm4, zmm4, DWORD PTR [rdi+16]{1to16}
	vpaddd zmm5, zmm5, DWORD PTR [rdi+20]{1to16}
	vpaddd zmm6, zmm6, DWORD PTR [rdi+24]{1to16}
	vpaddd zmm7, zmm7, DWORD PTR [rdi+28]{1to16}
	vpunpckldq zmm1, zmm4, zmm5
	vpunpckhdq zmm5, zmm4, zmm5
	vpunpckldq zmm15, zmm6, zmm7
	vpunpckhdq zmm7, zmm6, zmm7
	vpunpcklqdq zmm4, zmm1, zmm15
	vpunpckhqdq zmm1, zmm1, zmm15
	vpunpcklqdq zmm6, zmm5, zmm7
	vpunpckhqdq zmm7, zmm5, zmm7
	vpaddd zmm8, zmm8, DWORD PTR [rdi+32]{1to16}
	vpaddd zmm9, zmm9, DWORD PTR [rdi+36]{1to16}
	vpaddd zmm10, zmm10, DWORD PTR [rdi+40]{1to16}
	vpaddd zmm11, zmm11, DWORD PTR [rdi+44]{1to16}
	vpunpckldq zmm5, zmm8, zmm9
	vpunpckhdq zmm9, zmm8, zmm9
	vpunpckldq zmm15, zmm10, zmm11
	vpunpckhdq zmm11, zmm10, zmm11
	vpunpcklqdq zmm8, zmm5, zmm15
	vpunpckhqdq zmm5, zmm5, zmm15
	vpunpcklqdq zmm10, zmm9, zmm11
	vpunpckhqdq zmm11, zmm9, zmm11
	vmovdqu32 zmm9, ZMMWORD PTR [rcx]
	vmovdqu32 zmm15, ZMMWORD PTR [rcx+64]
	vmovdqu32 ZMMWORD PTR [rcx], zmm2
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm3
	vpaddd zmm12, zmm12, DWORD PTR [rdi+48]{1to16}
	vpaddd zmm13, zmm13, DWORD PTR [rdi+52]{1to16}
	vpaddd zmm9, zmm9, DWORD PTR [rdi+56]{1to16}
	vpaddd zmm15, zmm15, DWORD PTR [rdi+60]{1to16}
	vmovdqu32 zmm3, ZMMWORD PTR [rcx+128]
	vpaddd zmm12, zmm12, zmm3
	vpunpckldq zmm2, zmm12, zmm13
	vpunpckhdq zmm13, zmm12, zmm13
	vpunpckldq zmm3, zmm9, zmm15
	vpunpckhdq zmm15, zmm9, zmm15
	vpunpcklqdq zmm12, zmm2, zmm3
	vpunpckhqdq zmm2, zmm2, zmm3
	vpunpcklqdq zmm9, zmm13, zmm15
	vpunpckhqdq zmm15, zmm13, zmm15
	vshufi32x4 zmm13, zmm0, zmm4, 68
	vshufi32x4 zmm0, zmm0, zmm4, 238
	vshufi32x4 zmm3, zmm8, zmm12, 68
	vshufi32x4 zmm8, zmm8, zmm12, 238
	vshufi32x4 zmm4, zmm13, zmm3, 136
	vshufi32x4 zmm12, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm0, zmm8, 136
	vshufi32x4 zmm3, zmm0, zmm8, 221
	cmp r10, 64
	jb 281f
	vmovdqu32 zmm0, ZMMWORD PTR [r8]
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	jmp 282f
281:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
282:
	cmp r10, 320
	jb 283f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+256]
	vpxord zmm0, zmm0, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm0
	jmp 284f
283:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+256]
	vpxord zmm0, zmm0, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm0
284:
	cmp r10, 576
	jb 285f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+512]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm0
	jmp 286f
285:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+512]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm0
286:
	cmp r10, 832
	jb 287f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+768]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+768], zmm0
	jmp 288f
287:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+768]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+768], zmm0
288:
	vshufi32x4 zmm13, zmm14, zmm1, 68
	vshufi32x4 zmm14, zmm14, zmm1, 238
	vshufi32x4 zmm3, zmm5, zmm2, 68
	vshufi32x4 zmm5, zmm5, zmm2, 238
	vshufi32x4 zmm1, zmm13, zmm3, 136
	vshufi32x4 zmm2, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm14, zmm5, 136
	vshufi32x4 zmm3, zmm14, zmm5, 221
	cmp r10, 128
	jb 289f
	vmovdqu32 zmm14, ZMMWORD PTR [r8+64]
	vpxord zmm14, zmm14, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm14
	jmp 290f
289:
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+64]
	vpxord zmm14, zmm14, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm14
290:
	cmp r10, 384
	jb 291f
	vmovdqu32 zmm14, ZMMWORD PTR [r8+320]
	vpxord zmm14, zmm14, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm14
	jmp 292f
291:
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+320]
	vpxord zmm14, zmm14, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm14
292:
	cmp r10, 640
	jb 293f
	vmovdqu32 zmm14, ZMMWORD PTR [r8+576]
	vpxord zmm14, zmm14, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+576], zmm14
	jmp 294f
293:
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+576]
	vpxord zmm14, zmm14, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+576], zmm14
294:
	cmp r10, 896
	jb 295f
	vmovdqu32 zmm14, ZMMWORD PTR [r8+832]
	vpxord zmm14, zmm14, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+832], zmm14
	jmp 296f
295:
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+832]
	vpxord zmm14, zmm14, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+832], zmm14
296:
	vmovdqu32 zmm0, ZMMWORD PTR [rcx]
	vshufi32x4 zmm13, zmm0, zmm6, 68
	vshufi32x4 zmm0, zmm0, zmm6, 238
	vshufi32x4 zmm3, zmm10, zmm9, 68
	vshufi32x4 zmm10, zmm10, zmm9, 238
	vshufi32x4 zmm6, zmm13, zmm3, 136
	vshufi32x4 zmm9, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm0, zmm10, 136
	vshufi32x4 zmm3, zmm0, zmm10, 221
	cmp r10, 192
	jb 297f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+128]
	vpxord zmm0, zmm0, zmm6
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm0
	jmp 298f
297:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+128]
	vpxord zmm0, zmm0, zmm6
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm0
298:
	cmp r10, 448
	jb 299f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+384]
	vpxord zmm0, zmm0, zmm9
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm0
	jmp 2100f
299:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+384]
	vpxord zmm0, zmm0, zmm9
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm0
2100:
	cmp r10, 704
	jb 2101f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+640]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+640], zmm0
	jmp 2102f
2101:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+640]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+640], zmm0
2102:
	cmp r10, 960
	jb 2103f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+896]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+896], zmm0
	jmp 2104f
2103:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+896]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+896], zmm0
2104:
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+64]
	vshufi32x4 zmm13, zmm0, zmm7, 68
	vshufi32x4 zmm0, zmm0, zmm7, 238
	vshufi32x4 zmm3, zmm11, zmm15, 68
	vshufi32x4 zmm11, zmm11, zmm15, 238
	vshufi32x4 zmm7, zmm13, zmm3, 136
	vshufi32x4 zmm15, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm0, zmm11, 136
	vshufi32x4 zmm3, zmm0, zmm11, 221
	cmp r10, 256
	jb 2105f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+192]
	vpxord zmm0, zmm0, zmm7
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm0
	jmp 2106f
2105:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+192]
	vpxord zmm0, zmm0, zmm7
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm0
2106:
	cmp r10, 512
	jb 2107f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+448]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm0
	jmp 2108f
2107:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+448]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm0
2108:
	cmp r10, 768
	jb 2109f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+704]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+704], zmm0
	jmp 2110f
2109:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+704]
	vpxord zmm0, zmm0, zmm13
	vmovdqu32 ZMMWORD PTR [rsi+704], zmm0
2110:
	cmp r10, 1024
	jb 2111f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+960]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+960], zmm0
	jmp 2112f
2111:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+960]
	vpxord zmm0, zmm0, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+960], zmm0
2112:
	add r8, 1024
	mov eax, 0
	sub r10, 1024
	cmovb r10, rax
	mov eax, DWORD PTR [rdi+48]
	add eax, 16
	mov DWORD PTR [rdi+48], eax
	add rsi, 1024
	sub rdx, 1024
	cmp rdx, 1024
	jae 280b
	jmp 279f
278:
279:
	cmp rdx, 513
	jb 2113f
	mov r9, rcx
	vpbroadcastd zmm12, DWORD PTR [rdi+48]
	vpbroadcastd zmm13, DWORD PTR [rdi+52]
	vpbroadcastd zmm14, DWORD PTR [rdi+56]
	vpbroadcastd zmm15, DWORD PTR [rdi+60]
	vmovdqu32 zmm0, ZMMWORD PTR [r9+128]
	vpaddd zmm12, zmm12, zmm0
	vpbroadcastd zmm0, DWORD PTR [rdi]
	vpbroadcastd zmm1, DWORD PTR [rdi+4]
	vpbroadcastd zmm2, DWORD PTR [rdi+8]
	vpbroadcastd zmm3, DWORD PTR [rdi+12]
	vpbroadcastd zmm4, DWORD PTR [rdi+16]
	vpbroadcastd zmm5, DWORD PTR [rdi+20]
	vpbroadcastd zmm6, DWORD PTR [rdi+24]
	vpbroadcastd zmm7, DWORD PTR [rdi+28]
	vpbroadcastd zmm8, DWORD PTR [rdi+32]
	vpbroadcastd zmm9, DWORD PTR [rdi+36]
	vpbroadcastd zmm10, DWORD PTR [rdi+40]
	vpbroadcastd zmm11, DWORD PTR [rdi+44]
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vprold zmm15, zmm15, 16
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 12
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vpaddd zmm0, zmm0, zmm4
	vpaddd zmm1, zmm1, zmm5
	vpaddd zmm2, zmm2, zmm6
	vpaddd zmm3, zmm3, zmm7
	vpxord zmm12, zmm12, zmm0
	vpxord zmm13, zmm13, zmm1
	vpxord zmm14, zmm14, zmm2
	vpxord zmm15, zmm15, zmm3
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vprold zmm15, zmm15, 8
	vpaddd zmm8, zmm8, zmm12
	vpaddd zmm9, zmm9, zmm13
	vpaddd zmm10, zmm10, zmm14
	vpaddd zmm11, zmm11, zmm15
	vpxord zmm4, zmm4, zmm8
	vpxord zmm5, zmm5, zmm9
	vpxord zmm6, zmm6, zmm10
	vpxord zmm7, zmm7, zmm11
	vprold zmm4, zmm4, 7
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 16
	vprold zmm12, zmm12, 16
	vprold zmm13, zmm13, 16
	vprold zmm14, zmm14, 16
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 12
	vprold zmm6, zmm6, 12
	vprold zmm7, zmm7, 12
	vprold zmm4, zmm4, 12
	vpaddd zmm0, zmm0, zmm5
	vpaddd zmm1, zmm1, zmm6
	vpaddd zmm2, zmm2, zmm7
	vpaddd zmm3, zmm3, zmm4
	vpxord zmm15, zmm15, zmm0
	vpxord zmm12, zmm12, zmm1
	vpxord zmm13, zmm13, zmm2
	vpxord zmm14, zmm14, zmm3
	vprold zmm15, zmm15, 8
	vprold zmm12, zmm12, 8
	vprold zmm13, zmm13, 8
	vprold zmm14, zmm14, 8
	vpaddd zmm10, zmm10, zmm15
	vpaddd zmm11, zmm11, zmm12
	vpaddd zmm8, zmm8, zmm13
	vpaddd zmm9, zmm9, zmm14
	vpxord zmm5, zmm5, zmm10
	vpxord zmm6, zmm6, zmm11
	vpxord zmm7, zmm7, zmm8
	vpxord zmm4, zmm4, zmm9
	vprold zmm5, zmm5, 7
	vprold zmm6, zmm6, 7
	vprold zmm7, zmm7, 7
	vprold zmm4, zmm4, 7
	vmovdqu32 ZMMWORD PTR [r9], zmm14
	vmovdqu32 ZMMWORD PTR [r9+64], zmm15
	vpaddd zmm0, zmm0, DWORD PTR [rdi]{1to16}
	vpaddd zmm1, zmm1, DWORD PTR [rdi+4]{1to16}
	vpaddd zmm2, zmm2, DWORD PTR [rdi+8]{1to16}
	vpaddd zmm3, zmm3, DWORD PTR [rdi+12]{1to16}
	vpunpckldq zmm14, zmm0, zmm1
	vpunpckhdq zmm1, zmm0, zmm1
	vpunpckldq zmm15, zmm2, zmm3
	vpunpckhdq zmm3, zmm2, zmm3
	vpunpcklqdq zmm0, zmm14, zmm15
	vpunpckhqdq zmm14, zmm14, zmm15
	vpunpcklqdq zmm2, zmm1, zmm3
	vpunpckhqdq zmm3, zmm1, zmm3
	vpaddd zmm4, zmm4, DWORD PTR [rdi+16]{1to16}
	vpaddd zmm5, zmm5, DWORD PTR [rdi+20]{1to16}
	vpaddd zmm6, zmm6, DWORD PTR [rdi+24]{1to16}
	vpaddd zmm7, zmm7, DWORD PTR [rdi+28]{1to16}
	vpunpckldq zmm1, zmm4, zmm5
	vpunpckhdq zmm5, zmm4, zmm5
	vpunpckldq zmm15, zmm6, zmm7
	vpunpckhdq zmm7, zmm6, zmm7
	vpunpcklqdq zmm4, zmm1, zmm15
	vpunpckhqdq zmm1, zmm1, zmm15
	vpunpcklqdq zmm6, zmm5, zmm7
	vpunpckhqdq zmm7, zmm5, zmm7
	vpaddd zmm8, zmm8, DWORD PTR [rdi+32]{1to16}
	vpaddd zmm9, zmm9, DWORD PTR [rdi+36]{1to16}
	vpaddd zmm10, zmm10, DWORD PTR [rdi+40]{1to16}
	vpaddd zmm11, zmm11, DWORD PTR [rdi+44]{1to16}
	vpunpckldq zmm5, zmm8, zmm9
	vpunpckhdq zmm9, zmm8, zmm9
	vpunpckldq zmm15, zmm10, zmm11
	vpunpckhdq zmm11, zmm10, zmm11
	vpunpcklqdq zmm8, zmm5, zmm15
	vpunpckhqdq zmm5, zmm5, zmm15
	vpunpcklqdq zmm10, zmm9, zmm11
	vpunpckhqdq zmm11, zmm9, zmm11
	vmovdqu32 zmm9, ZMMWORD PTR [r9]
	vmovdqu32 zmm15, ZMMWORD PTR [r9+64]
	vmovdqu32 ZMMWORD PTR [r9], zmm2
	vmovdqu32 ZMMWORD PTR [r9+64], zmm3
	vpaddd zmm12, zmm12, DWORD PTR [rdi+48]{1to16}
	vpaddd zmm13, zmm13, DWORD PTR [rdi+52]{1to16}
	vpaddd zmm9, zmm9, DWORD PTR [rdi+56]{1to16}
	vpaddd zmm15, zmm15, DWORD PTR [rdi+60]{1to16}
	vmovdqu32 zmm3, ZMMWORD PTR [r9+128]
	vpaddd zmm12, zmm12, zmm3
	vpunpckldq zmm2, zmm12, zmm13
	vpunpckhdq zmm13, zmm12, zmm13
	vpunpckldq zmm3, zmm9, zmm15
	vpunpckhdq zmm15, zmm9, zmm15
	vpunpcklqdq zmm12, zmm2, zmm3
	vpunpckhqdq zmm2, zmm2, zmm3
	vpunpcklqdq zmm9, zmm13, zmm15
	vpunpckhqdq zmm15, zmm13, zmm15
	vshufi32x4 zmm13, zmm0, zmm4, 68
	vshufi32x4 zmm0, zmm0, zmm4, 238
	vshufi32x4 zmm3, zmm8, zmm12, 68
	vshufi32x4 zmm8, zmm8, zmm12, 238
	vshufi32x4 zmm4, zmm13, zmm3, 136
	vshufi32x4 zmm12, zmm13, zmm3, 221
	vshufi32x4 zmm13, zmm0, zmm8, 136
	vshufi32x4 zmm3, zmm0, zmm8, 221
	cmp r10, 64
	jb 2115f
	vmovdqu32 zmm0, ZMMWORD PTR [r8]
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	jmp 2116f
2115:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
2116:
	cmp r10, 320
	jb 2117f
	vmovdqu32 zmm0, ZMMWORD PTR [r8+256]
	vpxord zmm0, zmm0, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm0
	jmp 2118f
2117:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+256]
	vpxord zmm0, zmm0, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm0
2118:
	vshufi32x4 zmm0, zmm14, zmm1, 68
	vshufi32x4 zmm14, zmm14, zmm1, 238
	vshufi32x4 zmm8, zmm5, zmm2, 68
	vshufi32x4 zmm5, zmm5, zmm2, 238
	vshufi32x4 zmm1, zmm0, zmm8, 136
	vshufi32x4 zmm2, zmm0, zmm8, 221
	vshufi32x4 zmm0, zmm14, zmm5, 136
	vshufi32x4 zmm8, zmm14, zmm5, 221
	cmp r10, 128
	jb 2119f
	vmovdqu32 zmm14, ZMMWORD PTR [r8+64]
	vpxord zmm14, zmm14, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm14
	jmp 2120f
2119:
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+64]
	vpxord zmm14, zmm14, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm14
2120:
	cmp r10, 384
	jb 2121f
	vmovdqu32 zmm14, ZMMWORD PTR [r8+320]
	vpxord zmm14, zmm14, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm14
	jmp 2122f
2121:
	vmovdqu32 zmm14, ZMMWORD PTR [rsi+320]
	vpxord zmm14, zmm14, zmm2
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm14
2122:
	vmovdqu32 zmm4, ZMMWORD PTR [r9]
	vshufi32x4 zmm12, zmm4, zmm6, 68
	vshufi32x4 zmm4, zmm4, zmm6, 238
	vshufi32x4 zmm14, zmm10, zmm9, 68
	vshufi32x4 zmm10, zmm10, zmm9, 238
	vshufi32x4 zmm6, zmm12, zmm14, 136
	vshufi32x4 zmm9, zmm12, zmm14, 221
	vshufi32x4 zmm12, zmm4, zmm10, 136
	vshufi32x4 zmm14, zmm4, zmm10, 221
	cmp r10, 192
	jb 2123f
	vmovdqu32 zmm4, ZMMWORD PTR [r8+128]
	vpxord zmm4, zmm4, zmm6
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm4
	jmp 2124f
2123:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+128]
	vpxord zmm4, zmm4, zmm6
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm4
2124:
	cmp r10, 448
	jb 2125f
	vmovdqu32 zmm4, ZMMWORD PTR [r8+384]
	vpxord zmm4, zmm4, zmm9
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm4
	jmp 2126f
2125:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+384]
	vpxord zmm4, zmm4, zmm9
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm4
2126:
	vmovdqu32 zmm4, ZMMWORD PTR [r9+64]
	vshufi32x4 zmm5, zmm4, zmm7, 68
	vshufi32x4 zmm4, zmm4, zmm7, 238
	vshufi32x4 zmm1, zmm11, zmm15, 68
	vshufi32x4 zmm11, zmm11, zmm15, 238
	vshufi32x4 zmm7, zmm5, zmm1, 136
	vshufi32x4 zmm15, zmm5, zmm1, 221
	vshufi32x4 zmm5, zmm4, zmm11, 136
	vshufi32x4 zmm1, zmm4, zmm11, 221
	cmp r10, 256
	jb 2127f
	vmovdqu32 zmm4, ZMMWORD PTR [r8+192]
	vpxord zmm4, zmm4, zmm7
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm4
	jmp 2128f
2127:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+192]
	vpxord zmm4, zmm4, zmm7
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm4
2128:
	cmp r10, 512
	jb 2129f
	vmovdqu32 zmm4, ZMMWORD PTR [r8+448]
	vpxord zmm4, zmm4, zmm15
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm4
	jmp 2130f
2129:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+448]
	vpxord zmm4, zmm4, zmm15
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm4
2130:
	add rsi, 512
	sub rdx, 512
	add r8, 512
	mov eax, 0
	sub r10, 512
	cmovb r10, rax
	cmp rdx, 512
	jb 2131f
	cmp r10, 512
	jb 2133f
	vmovdqu32 zmm2, ZMMWORD PTR [r8+448]
	vpxord zmm2, zmm2, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm2
	jmp 2134f
2133:
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+448]
	vpxord zmm2, zmm2, zmm1
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm2
2134:
	jmp 2132f
2131:
	vmovdqu32 ZMMWORD PTR [r9], zmm1
2132:
	cmp rdx, 448
	jb 2135f
	cmp r10, 448
	jb 2137f
	vmovdqu32 zmm2, ZMMWORD PTR [r8+384]
	vpxord zmm2, zmm2, zmm14
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm2
	jmp 2138f
2137:
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+384]
	vpxord zmm2, zmm2, zmm14
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm2
2138:
	jmp 2136f
2135:
	vmovdqu32 ZMMWORD PTR [r9], zmm14
2136:
	cmp rdx, 384
	jb 2139f
	cmp r10, 384
	jb 2141f
	vmovdqu32 zmm2, ZMMWORD PTR [r8+320]
	vpxord zmm2, zmm2, zmm8
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm2
	jmp 2142f
2141:
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+320]
	vpxord zmm2, zmm2, zmm8
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm2
2142:
	jmp 2140f
2139:
	vmovdqu32 ZMMWORD PTR [r9], zmm8
2140:
	cmp rdx, 320
	jb 2143f
	cmp r10, 320
	jb 2145f
	vmovdqu32 zmm2, ZMMWORD PTR [r8+256]
	vpxord zmm2, zmm2, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm2
	jmp 2146f
2145:
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+256]
	vpxord zmm2, zmm2, zmm3
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm2
2146:
	jmp 2144f
2143:
	vmovdqu32 ZMMWORD PTR [r9], zmm3
2144:
	cmp rdx, 256
	jb 2147f
	cmp r10, 256
	jb 2149f
	vmovdqu32 zmm2, ZMMWORD PTR [r8+192]
	vpxord zmm2, zmm2, zmm5
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm2
	jmp 2150f
2149:
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+192]
	vpxord zmm2, zmm2, zmm5
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm2
2150:
	jmp 2148f
2147:
	vmovdqu32 ZMMWORD PTR [r9], zmm5
2148:
	cmp rdx, 192
	jb 2151f
	cmp r10, 192
	jb 2153f
	vmovdqu32 zmm2, ZMMWORD PTR [r8+128]
	vpxord zmm2, zmm2, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm2
	jmp 2154f
2153:
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+128]
	vpxord zmm2, zmm2, zmm12
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm2
2154:
	jmp 2152f
2151:
	vmovdqu32 ZMMWORD PTR [r9], zmm12
2152:
	cmp rdx, 128
	jb 2155f
	cmp r10, 128
	jb 2157f
	vmovdqu32 zmm2, ZMMWORD PTR [r8+64]
	vpxord zmm2, zmm2, zmm0
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm2
	jmp 2158f
2157:
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+64]
	vpxord zmm2, zmm2, zmm0
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm2
2158:
	jmp 2156f
2155:
	vmovdqu32 ZMMWORD PTR [r9], zmm0
2156:
	cmp rdx, 64
	jb 2159f
	cmp r10, 64
	jb 2161f
	vmovdqu32 zmm2, ZMMWORD PTR [r8]
	vpxord zmm2, zmm2, zmm13
	vmovdqu32 ZMMWORD PTR [rsi], zmm2
	jmp 2162f
2161:
	vmovdqu32 zmm2, ZMMWORD PTR [rsi]
	vpxord zmm2, zmm2, zmm13
	vmovdqu32 ZMMWORD PTR [rsi], zmm2
2162:
	jmp 2160f
2159:
	vmovdqu32 ZMMWORD PTR [r9], zmm13
2160:
	mov rax, rdx
	shr rax, 6
	shl rax, 6
	add rsi, rax
	sub rdx, rax
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 2163f
2165:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 2165b
	jmp 2164f
2163:
2164:
	cmp rcx, rdx
	je 2166f
2168:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 2168b
	jmp 2167f
2166:
2167:
	vzeroupper
	mov rsi, r9
	jmp 2114f
2113:
	call {vg_chacha20_xor_avx512}
2114:
	mov rsi, r15
	add rsi, 128
	jmp 238f
237:
	mov rsi, r15
	add rsi, 736
	mov rdx, r13
	mov ecx, 0
	mov rax, rdx
	shr rax, 6
	je 2169f
2171:
	vmovdqu32 zmm0, ZMMWORD PTR [r14+rcx*1]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+rcx*1]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [r14+rcx*1], zmm0
	add rcx, 64
	sub rax, 1
	jne 2171b
	jmp 2170f
2169:
2170:
	mov rdi, r14
	add rdi, rcx
	add rsi, rcx
	sub rdx, rcx
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 2172f
2174:
	mov r8, QWORD PTR [rdi+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rdi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 2174b
	jmp 2173f
2172:
2173:
	cmp rcx, rdx
	je 2175f
2177:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 2177b
	jmp 2176f
2175:
2176:
	mov rsi, r15
	add rsi, 128
238:
	mov r15, rsi
	sub r15, 128
	mov edx, 0
	cmp r13, 961
	jb 2178f
	mov rdx, r13
	and rdx, 1023
	add rdx, 63
	and rdx, -64
	cmp rdx, 961
	jb 2180f
	mov edx, 0
	jmp 2181f
2180:
2181:
	jmp 2179f
2178:
	mov rdx, r13
2179:
	add rdx, 64
	vpxord zmm0, zmm0, zmm0
	mov ecx, 0
2182:
	vmovdqu32 ZMMWORD PTR [r15+rcx*1+672], zmm0
	add rcx, 64
	cmp rcx, rdx
	jb 2182b
	vzeroupper
	mov rdi, r15
	add rdi, 448
	mov rsi, r14
	mov rdx, r13
	shr rdx, 4
	je 2183f
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 2184f
2183:
2184:
	mov rdx, r13
	and rdx, 15
	jne 2185f
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 592
	mov edx, 1
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
2186:
	mov rdi, r15
	add rdi, 448
	mov esi, 0
	mov rdx, r12
	call {vg_poly1305_finalize_scratch}
	mov r15, rdi
	sub r15, 448
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r13, QWORD PTR [r15+16]
	mov r14, QWORD PTR [r15+24]
	mov r12, QWORD PTR [r15+40]
	mov r15, QWORD PTR [r15+32]
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pxor xmm0, xmm0
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
	lea rsp, [rsp+1736]
	ret
225:
	jne 229f
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	movabs rax, 0
	mov eax, 0
	add rax, 1
	jmp 230f
229:
230:
	mov rsi, rbp
	sub rsi, rdx
	add rsi, rbx
	xor r9d, r9d
	cmp rdx, 8
	jb 231f
	mov rax, QWORD PTR [rsi]
	add rsi, 8
	sub rdx, 8
	je 233f
235:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 235b
	jmp 234f
233:
234:
	jmp 232f
231:
236:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 236b
	mov rax, r9
	xor r9d, r9d
232:
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 576
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], r9
	mov edx, 1
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 226b
2185:
	mov rsi, r13
	sub rsi, rdx
	add rsi, r14
	xor r9d, r9d
	cmp rdx, 8
	jb 2187f
	mov rax, QWORD PTR [rsi]
	add rsi, 8
	sub rdx, 8
	je 2189f
2191:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 2191b
	jmp 2190f
2189:
2190:
	jmp 2188f
2187:
2192:
	shl r9, 8
	movzx ecx, BYTE PTR [rsi+rdx*1-1]
	or r9, rcx
	sub rdx, 1
	jne 2192b
	mov rax, r9
	xor r9d, r9d
2188:
	mov rdi, r15
	add rdi, 448
	mov rsi, r15
	add rsi, 576
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], r9
	mov edx, 2
	call {vg_poly1305_blocks_avx512}
	mov r15, rdi
	sub r15, 448
	jmp 2186b
	.p2align 6
