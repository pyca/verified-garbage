// The functions of `src/rsa_pkcs1_sig.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_sign_precomputed_ifma512:
	lea rsp, [rsp-1192]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rsi
	mov QWORD PTR [rsp+128], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], r8
	mov QWORD PTR [rsp+152], r9
	mov r8, rsp
	add r8, 160
	mov rdx, QWORD PTR [rsp+1200]
	mov edx, edx
	mov rsi, QWORD PTR [rsp+1208]
	mov r9, QWORD PTR [rsp+1216]
	cmp edx, 0
	je 20f
	cmp edx, 1
	je 22f
	cmp edx, 2
	je 24f
	cmp edx, 3
	je 26f
	cmp edx, 4
	je 28f
	cmp edx, 5
	je 210f
	cmp edx, 6
	je 212f
	cmp edx, 7
	je 214f
	cmp edx, 8
	je 216f
	cmp edx, 9
	je 218f
	cmp edx, 10
	je 220f
	cmp edx, 11
	je 222f
	mov r10d, 2048
	mov r11d, 0
	jmp 223f
222:
	mov r10d, 83
	mov r11d, 64
223:
	jmp 221f
220:
	mov r10d, 67
	mov r11d, 48
221:
	jmp 219f
218:
	mov r10d, 51
	mov r11d, 32
219:
	jmp 217f
216:
	mov r10d, 47
	mov r11d, 28
217:
	jmp 215f
214:
	mov r10d, 51
	mov r11d, 32
215:
	jmp 213f
212:
	mov r10d, 47
	mov r11d, 28
213:
	jmp 211f
210:
	mov r10d, 83
	mov r11d, 64
211:
	jmp 29f
28:
	mov r10d, 67
	mov r11d, 48
29:
	jmp 27f
26:
	mov r10d, 51
	mov r11d, 32
27:
	jmp 25f
24:
	mov r10d, 47
	mov r11d, 28
25:
	jmp 23f
22:
	mov r10d, 35
	mov r11d, 20
23:
	jmp 21f
20:
	mov r10d, 34
	mov r11d, 16
21:
	cmp r9, r11
	jne 224f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 226f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
228:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 228b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 229f
	cmp edx, 1
	je 231f
	cmp edx, 2
	je 233f
	cmp edx, 3
	je 235f
	cmp edx, 4
	je 237f
	cmp edx, 5
	je 239f
	cmp edx, 6
	je 241f
	cmp edx, 7
	je 243f
	cmp edx, 8
	je 245f
	cmp edx, 9
	je 247f
	cmp edx, 10
	je 249f
	cmp edx, 11
	je 251f
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
232:
	jmp 230f
229:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
230:
253:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 253b
	mov eax, 1
	jmp 227f
226:
	mov eax, 0
227:
	jmp 225f
224:
	mov eax, 0
225:
	cmp eax, 0
	je 254f
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+120]
	mov rdx, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+144]
	mov r9, QWORD PTR [rsp+152]
	mov rax, rsp
	add rax, 160
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rcx
	mov rax, QWORD PTR [rsp+1224]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+1232]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+1240]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+1248]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+1256]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+1264]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+1272]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+1280]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+1288]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+1296]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+1304]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+1312]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rsp+1320]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+1328]
	mov QWORD PTR [rsp+120], rax
	call {vg_rsa_private_checked_precomputed_ifma512}
	mov r11, QWORD PTR [rsp+136]
	mov edx, 0
	mov r10, rsp
	add r10, 160
256:
	mov BYTE PTR [r10], dl
	add r10, 1
	sub r11, 1
	jne 256b
	jmp 255f
254:
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+120]
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
257:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 257b
255:
	lea rsp, [rsp+1192]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	mov r11d, 16
	test r11d, esp
	je 258f
	xor r11d, r11d
	lea rsp, [rsp-4080]
	mov QWORD PTR [rsp+4072], r11
	movdqu XMMWORD PTR [rsp+4056], xmm0
	vmovdqu YMMWORD PTR [rsp+4024], ymm0
	vmovdqu YMMWORD PTR [rsp+3992], ymm0
	vmovdqu YMMWORD PTR [rsp+3960], ymm0
	vmovdqu YMMWORD PTR [rsp+3928], ymm0
	vmovdqu YMMWORD PTR [rsp+3896], ymm0
	vmovdqu YMMWORD PTR [rsp+3864], ymm0
	vmovdqu YMMWORD PTR [rsp+3832], ymm0
	vmovdqu YMMWORD PTR [rsp+3800], ymm0
	vmovdqu YMMWORD PTR [rsp+3768], ymm0
	vmovdqu YMMWORD PTR [rsp+3736], ymm0
	vmovdqu YMMWORD PTR [rsp+3704], ymm0
	vmovdqu YMMWORD PTR [rsp+3672], ymm0
	vmovdqu YMMWORD PTR [rsp+3640], ymm0
	vmovdqu YMMWORD PTR [rsp+3608], ymm0
	vmovdqu YMMWORD PTR [rsp+3576], ymm0
	vmovdqu YMMWORD PTR [rsp+3544], ymm0
	vmovdqu YMMWORD PTR [rsp+3512], ymm0
	vmovdqu YMMWORD PTR [rsp+3480], ymm0
	vmovdqu YMMWORD PTR [rsp+3448], ymm0
	vmovdqu YMMWORD PTR [rsp+3416], ymm0
	vmovdqu YMMWORD PTR [rsp+3384], ymm0
	vmovdqu YMMWORD PTR [rsp+3352], ymm0
	vmovdqu YMMWORD PTR [rsp+3320], ymm0
	vmovdqu YMMWORD PTR [rsp+3288], ymm0
	vmovdqu YMMWORD PTR [rsp+3256], ymm0
	vmovdqu YMMWORD PTR [rsp+3224], ymm0
	vmovdqu YMMWORD PTR [rsp+3192], ymm0
	vmovdqu YMMWORD PTR [rsp+3160], ymm0
	vmovdqu YMMWORD PTR [rsp+3128], ymm0
	vmovdqu YMMWORD PTR [rsp+3096], ymm0
	vmovdqu YMMWORD PTR [rsp+3064], ymm0
	vmovdqu YMMWORD PTR [rsp+3032], ymm0
	vmovdqu YMMWORD PTR [rsp+3000], ymm0
	vmovdqu YMMWORD PTR [rsp+2968], ymm0
	vmovdqu YMMWORD PTR [rsp+2936], ymm0
	vmovdqu YMMWORD PTR [rsp+2904], ymm0
	vmovdqu YMMWORD PTR [rsp+2872], ymm0
	vmovdqu YMMWORD PTR [rsp+2840], ymm0
	vmovdqu YMMWORD PTR [rsp+2808], ymm0
	vmovdqu YMMWORD PTR [rsp+2776], ymm0
	vmovdqu YMMWORD PTR [rsp+2744], ymm0
	vmovdqu YMMWORD PTR [rsp+2712], ymm0
	vmovdqu YMMWORD PTR [rsp+2680], ymm0
	vmovdqu YMMWORD PTR [rsp+2648], ymm0
	vmovdqu YMMWORD PTR [rsp+2616], ymm0
	vmovdqu YMMWORD PTR [rsp+2584], ymm0
	vmovdqu YMMWORD PTR [rsp+2552], ymm0
	vmovdqu YMMWORD PTR [rsp+2520], ymm0
	vmovdqu YMMWORD PTR [rsp+2488], ymm0
	vmovdqu YMMWORD PTR [rsp+2456], ymm0
	vmovdqu YMMWORD PTR [rsp+2424], ymm0
	vmovdqu YMMWORD PTR [rsp+2392], ymm0
	vmovdqu YMMWORD PTR [rsp+2360], ymm0
	vmovdqu YMMWORD PTR [rsp+2328], ymm0
	vmovdqu YMMWORD PTR [rsp+2296], ymm0
	vmovdqu YMMWORD PTR [rsp+2264], ymm0
	vmovdqu YMMWORD PTR [rsp+2232], ymm0
	vmovdqu YMMWORD PTR [rsp+2200], ymm0
	vmovdqu YMMWORD PTR [rsp+2168], ymm0
	vmovdqu YMMWORD PTR [rsp+2136], ymm0
	vmovdqu YMMWORD PTR [rsp+2104], ymm0
	vmovdqu YMMWORD PTR [rsp+2072], ymm0
	vmovdqu YMMWORD PTR [rsp+2040], ymm0
	vmovdqu YMMWORD PTR [rsp+2008], ymm0
	vmovdqu YMMWORD PTR [rsp+1976], ymm0
	vmovdqu YMMWORD PTR [rsp+1944], ymm0
	vmovdqu YMMWORD PTR [rsp+1912], ymm0
	vmovdqu YMMWORD PTR [rsp+1880], ymm0
	vmovdqu YMMWORD PTR [rsp+1848], ymm0
	vmovdqu YMMWORD PTR [rsp+1816], ymm0
	vmovdqu YMMWORD PTR [rsp+1784], ymm0
	vmovdqu YMMWORD PTR [rsp+1752], ymm0
	vmovdqu YMMWORD PTR [rsp+1720], ymm0
	vmovdqu YMMWORD PTR [rsp+1688], ymm0
	vmovdqu YMMWORD PTR [rsp+1656], ymm0
	vmovdqu YMMWORD PTR [rsp+1624], ymm0
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-376]
	mov QWORD PTR [rsp+368], r11
	vmovdqu YMMWORD PTR [rsp+336], ymm0
	vmovdqu YMMWORD PTR [rsp+304], ymm0
	vmovdqu YMMWORD PTR [rsp+272], ymm0
	vmovdqu YMMWORD PTR [rsp+240], ymm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+376]
	lea rsp, [rsp+4080]
	jmp 259f
258:
	xor r11d, r11d
	lea rsp, [rsp-4080]
	mov QWORD PTR [rsp+4072], r11
	vmovdqu YMMWORD PTR [rsp+4040], ymm0
	vmovdqu YMMWORD PTR [rsp+4008], ymm0
	vmovdqu YMMWORD PTR [rsp+3976], ymm0
	vmovdqu YMMWORD PTR [rsp+3944], ymm0
	vmovdqu YMMWORD PTR [rsp+3912], ymm0
	vmovdqu YMMWORD PTR [rsp+3880], ymm0
	vmovdqu YMMWORD PTR [rsp+3848], ymm0
	vmovdqu YMMWORD PTR [rsp+3816], ymm0
	vmovdqu YMMWORD PTR [rsp+3784], ymm0
	vmovdqu YMMWORD PTR [rsp+3752], ymm0
	vmovdqu YMMWORD PTR [rsp+3720], ymm0
	vmovdqu YMMWORD PTR [rsp+3688], ymm0
	vmovdqu YMMWORD PTR [rsp+3656], ymm0
	vmovdqu YMMWORD PTR [rsp+3624], ymm0
	vmovdqu YMMWORD PTR [rsp+3592], ymm0
	vmovdqu YMMWORD PTR [rsp+3560], ymm0
	vmovdqu YMMWORD PTR [rsp+3528], ymm0
	vmovdqu YMMWORD PTR [rsp+3496], ymm0
	vmovdqu YMMWORD PTR [rsp+3464], ymm0
	vmovdqu YMMWORD PTR [rsp+3432], ymm0
	vmovdqu YMMWORD PTR [rsp+3400], ymm0
	vmovdqu YMMWORD PTR [rsp+3368], ymm0
	vmovdqu YMMWORD PTR [rsp+3336], ymm0
	vmovdqu YMMWORD PTR [rsp+3304], ymm0
	vmovdqu YMMWORD PTR [rsp+3272], ymm0
	vmovdqu YMMWORD PTR [rsp+3240], ymm0
	vmovdqu YMMWORD PTR [rsp+3208], ymm0
	vmovdqu YMMWORD PTR [rsp+3176], ymm0
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
	vmovdqu YMMWORD PTR [rsp+3112], ymm0
	vmovdqu YMMWORD PTR [rsp+3080], ymm0
	vmovdqu YMMWORD PTR [rsp+3048], ymm0
	vmovdqu YMMWORD PTR [rsp+3016], ymm0
	vmovdqu YMMWORD PTR [rsp+2984], ymm0
	vmovdqu YMMWORD PTR [rsp+2952], ymm0
	vmovdqu YMMWORD PTR [rsp+2920], ymm0
	vmovdqu YMMWORD PTR [rsp+2888], ymm0
	vmovdqu YMMWORD PTR [rsp+2856], ymm0
	vmovdqu YMMWORD PTR [rsp+2824], ymm0
	vmovdqu YMMWORD PTR [rsp+2792], ymm0
	vmovdqu YMMWORD PTR [rsp+2760], ymm0
	vmovdqu YMMWORD PTR [rsp+2728], ymm0
	vmovdqu YMMWORD PTR [rsp+2696], ymm0
	vmovdqu YMMWORD PTR [rsp+2664], ymm0
	vmovdqu YMMWORD PTR [rsp+2632], ymm0
	vmovdqu YMMWORD PTR [rsp+2600], ymm0
	vmovdqu YMMWORD PTR [rsp+2568], ymm0
	vmovdqu YMMWORD PTR [rsp+2536], ymm0
	vmovdqu YMMWORD PTR [rsp+2504], ymm0
	vmovdqu YMMWORD PTR [rsp+2472], ymm0
	vmovdqu YMMWORD PTR [rsp+2440], ymm0
	vmovdqu YMMWORD PTR [rsp+2408], ymm0
	vmovdqu YMMWORD PTR [rsp+2376], ymm0
	vmovdqu YMMWORD PTR [rsp+2344], ymm0
	vmovdqu YMMWORD PTR [rsp+2312], ymm0
	vmovdqu YMMWORD PTR [rsp+2280], ymm0
	vmovdqu YMMWORD PTR [rsp+2248], ymm0
	vmovdqu YMMWORD PTR [rsp+2216], ymm0
	vmovdqu YMMWORD PTR [rsp+2184], ymm0
	vmovdqu YMMWORD PTR [rsp+2152], ymm0
	vmovdqu YMMWORD PTR [rsp+2120], ymm0
	vmovdqu YMMWORD PTR [rsp+2088], ymm0
	vmovdqu YMMWORD PTR [rsp+2056], ymm0
	vmovdqu YMMWORD PTR [rsp+2024], ymm0
	vmovdqu YMMWORD PTR [rsp+1992], ymm0
	vmovdqu YMMWORD PTR [rsp+1960], ymm0
	vmovdqu YMMWORD PTR [rsp+1928], ymm0
	vmovdqu YMMWORD PTR [rsp+1896], ymm0
	vmovdqu YMMWORD PTR [rsp+1864], ymm0
	vmovdqu YMMWORD PTR [rsp+1832], ymm0
	vmovdqu YMMWORD PTR [rsp+1800], ymm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-376]
	mov QWORD PTR [rsp+368], r11
	movdqu XMMWORD PTR [rsp+352], xmm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+376]
	lea rsp, [rsp+4080]
259:
	mov eax, eax
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

vg_rsa_pkcs1_sign_precomputed_ifma:
	lea rsp, [rsp-1192]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rsi
	mov QWORD PTR [rsp+128], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], r8
	mov QWORD PTR [rsp+152], r9
	mov r8, rsp
	add r8, 160
	mov rdx, QWORD PTR [rsp+1200]
	mov edx, edx
	mov rsi, QWORD PTR [rsp+1208]
	mov r9, QWORD PTR [rsp+1216]
	cmp edx, 0
	je 20f
	cmp edx, 1
	je 22f
	cmp edx, 2
	je 24f
	cmp edx, 3
	je 26f
	cmp edx, 4
	je 28f
	cmp edx, 5
	je 210f
	cmp edx, 6
	je 212f
	cmp edx, 7
	je 214f
	cmp edx, 8
	je 216f
	cmp edx, 9
	je 218f
	cmp edx, 10
	je 220f
	cmp edx, 11
	je 222f
	mov r10d, 2048
	mov r11d, 0
	jmp 223f
222:
	mov r10d, 83
	mov r11d, 64
223:
	jmp 221f
220:
	mov r10d, 67
	mov r11d, 48
221:
	jmp 219f
218:
	mov r10d, 51
	mov r11d, 32
219:
	jmp 217f
216:
	mov r10d, 47
	mov r11d, 28
217:
	jmp 215f
214:
	mov r10d, 51
	mov r11d, 32
215:
	jmp 213f
212:
	mov r10d, 47
	mov r11d, 28
213:
	jmp 211f
210:
	mov r10d, 83
	mov r11d, 64
211:
	jmp 29f
28:
	mov r10d, 67
	mov r11d, 48
29:
	jmp 27f
26:
	mov r10d, 51
	mov r11d, 32
27:
	jmp 25f
24:
	mov r10d, 47
	mov r11d, 28
25:
	jmp 23f
22:
	mov r10d, 35
	mov r11d, 20
23:
	jmp 21f
20:
	mov r10d, 34
	mov r11d, 16
21:
	cmp r9, r11
	jne 224f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 226f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
228:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 228b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 229f
	cmp edx, 1
	je 231f
	cmp edx, 2
	je 233f
	cmp edx, 3
	je 235f
	cmp edx, 4
	je 237f
	cmp edx, 5
	je 239f
	cmp edx, 6
	je 241f
	cmp edx, 7
	je 243f
	cmp edx, 8
	je 245f
	cmp edx, 9
	je 247f
	cmp edx, 10
	je 249f
	cmp edx, 11
	je 251f
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
232:
	jmp 230f
229:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
230:
253:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 253b
	mov eax, 1
	jmp 227f
226:
	mov eax, 0
227:
	jmp 225f
224:
	mov eax, 0
225:
	cmp eax, 0
	je 254f
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+120]
	mov rdx, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+144]
	mov r9, QWORD PTR [rsp+152]
	mov rax, rsp
	add rax, 160
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rcx
	mov rax, QWORD PTR [rsp+1224]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+1232]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+1240]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+1248]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+1256]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+1264]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+1272]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+1280]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+1288]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+1296]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+1304]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+1312]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rsp+1320]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+1328]
	mov QWORD PTR [rsp+120], rax
	call {vg_rsa_private_checked_precomputed_ifma}
	mov r11, QWORD PTR [rsp+136]
	mov edx, 0
	mov r10, rsp
	add r10, 160
256:
	mov BYTE PTR [r10], dl
	add r10, 1
	sub r11, 1
	jne 256b
	jmp 255f
254:
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+120]
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
257:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 257b
255:
	lea rsp, [rsp+1192]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	mov r11d, 16
	test r11d, esp
	je 258f
	xor r11d, r11d
	lea rsp, [rsp-4080]
	mov QWORD PTR [rsp+4072], r11
	movdqu XMMWORD PTR [rsp+4056], xmm0
	vmovdqu YMMWORD PTR [rsp+4024], ymm0
	vmovdqu YMMWORD PTR [rsp+3992], ymm0
	vmovdqu YMMWORD PTR [rsp+3960], ymm0
	vmovdqu YMMWORD PTR [rsp+3928], ymm0
	vmovdqu YMMWORD PTR [rsp+3896], ymm0
	vmovdqu YMMWORD PTR [rsp+3864], ymm0
	vmovdqu YMMWORD PTR [rsp+3832], ymm0
	vmovdqu YMMWORD PTR [rsp+3800], ymm0
	vmovdqu YMMWORD PTR [rsp+3768], ymm0
	vmovdqu YMMWORD PTR [rsp+3736], ymm0
	vmovdqu YMMWORD PTR [rsp+3704], ymm0
	vmovdqu YMMWORD PTR [rsp+3672], ymm0
	vmovdqu YMMWORD PTR [rsp+3640], ymm0
	vmovdqu YMMWORD PTR [rsp+3608], ymm0
	vmovdqu YMMWORD PTR [rsp+3576], ymm0
	vmovdqu YMMWORD PTR [rsp+3544], ymm0
	vmovdqu YMMWORD PTR [rsp+3512], ymm0
	vmovdqu YMMWORD PTR [rsp+3480], ymm0
	vmovdqu YMMWORD PTR [rsp+3448], ymm0
	vmovdqu YMMWORD PTR [rsp+3416], ymm0
	vmovdqu YMMWORD PTR [rsp+3384], ymm0
	vmovdqu YMMWORD PTR [rsp+3352], ymm0
	vmovdqu YMMWORD PTR [rsp+3320], ymm0
	vmovdqu YMMWORD PTR [rsp+3288], ymm0
	vmovdqu YMMWORD PTR [rsp+3256], ymm0
	vmovdqu YMMWORD PTR [rsp+3224], ymm0
	vmovdqu YMMWORD PTR [rsp+3192], ymm0
	vmovdqu YMMWORD PTR [rsp+3160], ymm0
	vmovdqu YMMWORD PTR [rsp+3128], ymm0
	vmovdqu YMMWORD PTR [rsp+3096], ymm0
	vmovdqu YMMWORD PTR [rsp+3064], ymm0
	vmovdqu YMMWORD PTR [rsp+3032], ymm0
	vmovdqu YMMWORD PTR [rsp+3000], ymm0
	vmovdqu YMMWORD PTR [rsp+2968], ymm0
	vmovdqu YMMWORD PTR [rsp+2936], ymm0
	vmovdqu YMMWORD PTR [rsp+2904], ymm0
	vmovdqu YMMWORD PTR [rsp+2872], ymm0
	vmovdqu YMMWORD PTR [rsp+2840], ymm0
	vmovdqu YMMWORD PTR [rsp+2808], ymm0
	vmovdqu YMMWORD PTR [rsp+2776], ymm0
	vmovdqu YMMWORD PTR [rsp+2744], ymm0
	vmovdqu YMMWORD PTR [rsp+2712], ymm0
	vmovdqu YMMWORD PTR [rsp+2680], ymm0
	vmovdqu YMMWORD PTR [rsp+2648], ymm0
	vmovdqu YMMWORD PTR [rsp+2616], ymm0
	vmovdqu YMMWORD PTR [rsp+2584], ymm0
	vmovdqu YMMWORD PTR [rsp+2552], ymm0
	vmovdqu YMMWORD PTR [rsp+2520], ymm0
	vmovdqu YMMWORD PTR [rsp+2488], ymm0
	vmovdqu YMMWORD PTR [rsp+2456], ymm0
	vmovdqu YMMWORD PTR [rsp+2424], ymm0
	vmovdqu YMMWORD PTR [rsp+2392], ymm0
	vmovdqu YMMWORD PTR [rsp+2360], ymm0
	vmovdqu YMMWORD PTR [rsp+2328], ymm0
	vmovdqu YMMWORD PTR [rsp+2296], ymm0
	vmovdqu YMMWORD PTR [rsp+2264], ymm0
	vmovdqu YMMWORD PTR [rsp+2232], ymm0
	vmovdqu YMMWORD PTR [rsp+2200], ymm0
	vmovdqu YMMWORD PTR [rsp+2168], ymm0
	vmovdqu YMMWORD PTR [rsp+2136], ymm0
	vmovdqu YMMWORD PTR [rsp+2104], ymm0
	vmovdqu YMMWORD PTR [rsp+2072], ymm0
	vmovdqu YMMWORD PTR [rsp+2040], ymm0
	vmovdqu YMMWORD PTR [rsp+2008], ymm0
	vmovdqu YMMWORD PTR [rsp+1976], ymm0
	vmovdqu YMMWORD PTR [rsp+1944], ymm0
	vmovdqu YMMWORD PTR [rsp+1912], ymm0
	vmovdqu YMMWORD PTR [rsp+1880], ymm0
	vmovdqu YMMWORD PTR [rsp+1848], ymm0
	vmovdqu YMMWORD PTR [rsp+1816], ymm0
	vmovdqu YMMWORD PTR [rsp+1784], ymm0
	vmovdqu YMMWORD PTR [rsp+1752], ymm0
	vmovdqu YMMWORD PTR [rsp+1720], ymm0
	vmovdqu YMMWORD PTR [rsp+1688], ymm0
	vmovdqu YMMWORD PTR [rsp+1656], ymm0
	vmovdqu YMMWORD PTR [rsp+1624], ymm0
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-376]
	mov QWORD PTR [rsp+368], r11
	vmovdqu YMMWORD PTR [rsp+336], ymm0
	vmovdqu YMMWORD PTR [rsp+304], ymm0
	vmovdqu YMMWORD PTR [rsp+272], ymm0
	vmovdqu YMMWORD PTR [rsp+240], ymm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+376]
	lea rsp, [rsp+4080]
	jmp 259f
258:
	xor r11d, r11d
	lea rsp, [rsp-4080]
	mov QWORD PTR [rsp+4072], r11
	vmovdqu YMMWORD PTR [rsp+4040], ymm0
	vmovdqu YMMWORD PTR [rsp+4008], ymm0
	vmovdqu YMMWORD PTR [rsp+3976], ymm0
	vmovdqu YMMWORD PTR [rsp+3944], ymm0
	vmovdqu YMMWORD PTR [rsp+3912], ymm0
	vmovdqu YMMWORD PTR [rsp+3880], ymm0
	vmovdqu YMMWORD PTR [rsp+3848], ymm0
	vmovdqu YMMWORD PTR [rsp+3816], ymm0
	vmovdqu YMMWORD PTR [rsp+3784], ymm0
	vmovdqu YMMWORD PTR [rsp+3752], ymm0
	vmovdqu YMMWORD PTR [rsp+3720], ymm0
	vmovdqu YMMWORD PTR [rsp+3688], ymm0
	vmovdqu YMMWORD PTR [rsp+3656], ymm0
	vmovdqu YMMWORD PTR [rsp+3624], ymm0
	vmovdqu YMMWORD PTR [rsp+3592], ymm0
	vmovdqu YMMWORD PTR [rsp+3560], ymm0
	vmovdqu YMMWORD PTR [rsp+3528], ymm0
	vmovdqu YMMWORD PTR [rsp+3496], ymm0
	vmovdqu YMMWORD PTR [rsp+3464], ymm0
	vmovdqu YMMWORD PTR [rsp+3432], ymm0
	vmovdqu YMMWORD PTR [rsp+3400], ymm0
	vmovdqu YMMWORD PTR [rsp+3368], ymm0
	vmovdqu YMMWORD PTR [rsp+3336], ymm0
	vmovdqu YMMWORD PTR [rsp+3304], ymm0
	vmovdqu YMMWORD PTR [rsp+3272], ymm0
	vmovdqu YMMWORD PTR [rsp+3240], ymm0
	vmovdqu YMMWORD PTR [rsp+3208], ymm0
	vmovdqu YMMWORD PTR [rsp+3176], ymm0
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
	vmovdqu YMMWORD PTR [rsp+3112], ymm0
	vmovdqu YMMWORD PTR [rsp+3080], ymm0
	vmovdqu YMMWORD PTR [rsp+3048], ymm0
	vmovdqu YMMWORD PTR [rsp+3016], ymm0
	vmovdqu YMMWORD PTR [rsp+2984], ymm0
	vmovdqu YMMWORD PTR [rsp+2952], ymm0
	vmovdqu YMMWORD PTR [rsp+2920], ymm0
	vmovdqu YMMWORD PTR [rsp+2888], ymm0
	vmovdqu YMMWORD PTR [rsp+2856], ymm0
	vmovdqu YMMWORD PTR [rsp+2824], ymm0
	vmovdqu YMMWORD PTR [rsp+2792], ymm0
	vmovdqu YMMWORD PTR [rsp+2760], ymm0
	vmovdqu YMMWORD PTR [rsp+2728], ymm0
	vmovdqu YMMWORD PTR [rsp+2696], ymm0
	vmovdqu YMMWORD PTR [rsp+2664], ymm0
	vmovdqu YMMWORD PTR [rsp+2632], ymm0
	vmovdqu YMMWORD PTR [rsp+2600], ymm0
	vmovdqu YMMWORD PTR [rsp+2568], ymm0
	vmovdqu YMMWORD PTR [rsp+2536], ymm0
	vmovdqu YMMWORD PTR [rsp+2504], ymm0
	vmovdqu YMMWORD PTR [rsp+2472], ymm0
	vmovdqu YMMWORD PTR [rsp+2440], ymm0
	vmovdqu YMMWORD PTR [rsp+2408], ymm0
	vmovdqu YMMWORD PTR [rsp+2376], ymm0
	vmovdqu YMMWORD PTR [rsp+2344], ymm0
	vmovdqu YMMWORD PTR [rsp+2312], ymm0
	vmovdqu YMMWORD PTR [rsp+2280], ymm0
	vmovdqu YMMWORD PTR [rsp+2248], ymm0
	vmovdqu YMMWORD PTR [rsp+2216], ymm0
	vmovdqu YMMWORD PTR [rsp+2184], ymm0
	vmovdqu YMMWORD PTR [rsp+2152], ymm0
	vmovdqu YMMWORD PTR [rsp+2120], ymm0
	vmovdqu YMMWORD PTR [rsp+2088], ymm0
	vmovdqu YMMWORD PTR [rsp+2056], ymm0
	vmovdqu YMMWORD PTR [rsp+2024], ymm0
	vmovdqu YMMWORD PTR [rsp+1992], ymm0
	vmovdqu YMMWORD PTR [rsp+1960], ymm0
	vmovdqu YMMWORD PTR [rsp+1928], ymm0
	vmovdqu YMMWORD PTR [rsp+1896], ymm0
	vmovdqu YMMWORD PTR [rsp+1864], ymm0
	vmovdqu YMMWORD PTR [rsp+1832], ymm0
	vmovdqu YMMWORD PTR [rsp+1800], ymm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-376]
	mov QWORD PTR [rsp+368], r11
	movdqu XMMWORD PTR [rsp+352], xmm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+376]
	lea rsp, [rsp+4080]
259:
	mov eax, eax
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

vg_rsa_pkcs1_sign_precomputed_adx:
	lea rsp, [rsp-1192]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rsi
	mov QWORD PTR [rsp+128], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], r8
	mov QWORD PTR [rsp+152], r9
	mov r8, rsp
	add r8, 160
	mov rdx, QWORD PTR [rsp+1200]
	mov edx, edx
	mov rsi, QWORD PTR [rsp+1208]
	mov r9, QWORD PTR [rsp+1216]
	cmp edx, 0
	je 20f
	cmp edx, 1
	je 22f
	cmp edx, 2
	je 24f
	cmp edx, 3
	je 26f
	cmp edx, 4
	je 28f
	cmp edx, 5
	je 210f
	cmp edx, 6
	je 212f
	cmp edx, 7
	je 214f
	cmp edx, 8
	je 216f
	cmp edx, 9
	je 218f
	cmp edx, 10
	je 220f
	cmp edx, 11
	je 222f
	mov r10d, 2048
	mov r11d, 0
	jmp 223f
222:
	mov r10d, 83
	mov r11d, 64
223:
	jmp 221f
220:
	mov r10d, 67
	mov r11d, 48
221:
	jmp 219f
218:
	mov r10d, 51
	mov r11d, 32
219:
	jmp 217f
216:
	mov r10d, 47
	mov r11d, 28
217:
	jmp 215f
214:
	mov r10d, 51
	mov r11d, 32
215:
	jmp 213f
212:
	mov r10d, 47
	mov r11d, 28
213:
	jmp 211f
210:
	mov r10d, 83
	mov r11d, 64
211:
	jmp 29f
28:
	mov r10d, 67
	mov r11d, 48
29:
	jmp 27f
26:
	mov r10d, 51
	mov r11d, 32
27:
	jmp 25f
24:
	mov r10d, 47
	mov r11d, 28
25:
	jmp 23f
22:
	mov r10d, 35
	mov r11d, 20
23:
	jmp 21f
20:
	mov r10d, 34
	mov r11d, 16
21:
	cmp r9, r11
	jne 224f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 226f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
228:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 228b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 229f
	cmp edx, 1
	je 231f
	cmp edx, 2
	je 233f
	cmp edx, 3
	je 235f
	cmp edx, 4
	je 237f
	cmp edx, 5
	je 239f
	cmp edx, 6
	je 241f
	cmp edx, 7
	je 243f
	cmp edx, 8
	je 245f
	cmp edx, 9
	je 247f
	cmp edx, 10
	je 249f
	cmp edx, 11
	je 251f
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
232:
	jmp 230f
229:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
230:
253:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 253b
	mov eax, 1
	jmp 227f
226:
	mov eax, 0
227:
	jmp 225f
224:
	mov eax, 0
225:
	cmp eax, 0
	je 254f
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+120]
	mov rdx, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+144]
	mov r9, QWORD PTR [rsp+152]
	mov rax, rsp
	add rax, 160
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rcx
	mov rax, QWORD PTR [rsp+1224]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+1232]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+1240]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+1248]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+1256]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+1264]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+1272]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+1280]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+1288]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+1296]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+1304]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+1312]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rsp+1320]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+1328]
	mov QWORD PTR [rsp+120], rax
	call {vg_rsa_private_checked_precomputed_adx}
	mov r11, QWORD PTR [rsp+136]
	mov edx, 0
	mov r10, rsp
	add r10, 160
256:
	mov BYTE PTR [r10], dl
	add r10, 1
	sub r11, 1
	jne 256b
	jmp 255f
254:
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+120]
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
257:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 257b
255:
	lea rsp, [rsp+1192]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 258f
	xor r11d, r11d
	lea rsp, [rsp-4080]
	mov QWORD PTR [rsp+4072], r11
	movdqu XMMWORD PTR [rsp+4056], xmm0
	vmovdqu YMMWORD PTR [rsp+4024], ymm0
	vmovdqu YMMWORD PTR [rsp+3992], ymm0
	vmovdqu YMMWORD PTR [rsp+3960], ymm0
	vmovdqu YMMWORD PTR [rsp+3928], ymm0
	vmovdqu YMMWORD PTR [rsp+3896], ymm0
	vmovdqu YMMWORD PTR [rsp+3864], ymm0
	vmovdqu YMMWORD PTR [rsp+3832], ymm0
	vmovdqu YMMWORD PTR [rsp+3800], ymm0
	vmovdqu YMMWORD PTR [rsp+3768], ymm0
	vmovdqu YMMWORD PTR [rsp+3736], ymm0
	vmovdqu YMMWORD PTR [rsp+3704], ymm0
	vmovdqu YMMWORD PTR [rsp+3672], ymm0
	vmovdqu YMMWORD PTR [rsp+3640], ymm0
	vmovdqu YMMWORD PTR [rsp+3608], ymm0
	vmovdqu YMMWORD PTR [rsp+3576], ymm0
	vmovdqu YMMWORD PTR [rsp+3544], ymm0
	vmovdqu YMMWORD PTR [rsp+3512], ymm0
	vmovdqu YMMWORD PTR [rsp+3480], ymm0
	vmovdqu YMMWORD PTR [rsp+3448], ymm0
	vmovdqu YMMWORD PTR [rsp+3416], ymm0
	vmovdqu YMMWORD PTR [rsp+3384], ymm0
	vmovdqu YMMWORD PTR [rsp+3352], ymm0
	vmovdqu YMMWORD PTR [rsp+3320], ymm0
	vmovdqu YMMWORD PTR [rsp+3288], ymm0
	vmovdqu YMMWORD PTR [rsp+3256], ymm0
	vmovdqu YMMWORD PTR [rsp+3224], ymm0
	vmovdqu YMMWORD PTR [rsp+3192], ymm0
	vmovdqu YMMWORD PTR [rsp+3160], ymm0
	vmovdqu YMMWORD PTR [rsp+3128], ymm0
	vmovdqu YMMWORD PTR [rsp+3096], ymm0
	vmovdqu YMMWORD PTR [rsp+3064], ymm0
	vmovdqu YMMWORD PTR [rsp+3032], ymm0
	vmovdqu YMMWORD PTR [rsp+3000], ymm0
	vmovdqu YMMWORD PTR [rsp+2968], ymm0
	vmovdqu YMMWORD PTR [rsp+2936], ymm0
	vmovdqu YMMWORD PTR [rsp+2904], ymm0
	vmovdqu YMMWORD PTR [rsp+2872], ymm0
	vmovdqu YMMWORD PTR [rsp+2840], ymm0
	vmovdqu YMMWORD PTR [rsp+2808], ymm0
	vmovdqu YMMWORD PTR [rsp+2776], ymm0
	vmovdqu YMMWORD PTR [rsp+2744], ymm0
	vmovdqu YMMWORD PTR [rsp+2712], ymm0
	vmovdqu YMMWORD PTR [rsp+2680], ymm0
	vmovdqu YMMWORD PTR [rsp+2648], ymm0
	vmovdqu YMMWORD PTR [rsp+2616], ymm0
	vmovdqu YMMWORD PTR [rsp+2584], ymm0
	vmovdqu YMMWORD PTR [rsp+2552], ymm0
	vmovdqu YMMWORD PTR [rsp+2520], ymm0
	vmovdqu YMMWORD PTR [rsp+2488], ymm0
	vmovdqu YMMWORD PTR [rsp+2456], ymm0
	vmovdqu YMMWORD PTR [rsp+2424], ymm0
	vmovdqu YMMWORD PTR [rsp+2392], ymm0
	vmovdqu YMMWORD PTR [rsp+2360], ymm0
	vmovdqu YMMWORD PTR [rsp+2328], ymm0
	vmovdqu YMMWORD PTR [rsp+2296], ymm0
	vmovdqu YMMWORD PTR [rsp+2264], ymm0
	vmovdqu YMMWORD PTR [rsp+2232], ymm0
	vmovdqu YMMWORD PTR [rsp+2200], ymm0
	vmovdqu YMMWORD PTR [rsp+2168], ymm0
	vmovdqu YMMWORD PTR [rsp+2136], ymm0
	vmovdqu YMMWORD PTR [rsp+2104], ymm0
	vmovdqu YMMWORD PTR [rsp+2072], ymm0
	vmovdqu YMMWORD PTR [rsp+2040], ymm0
	vmovdqu YMMWORD PTR [rsp+2008], ymm0
	vmovdqu YMMWORD PTR [rsp+1976], ymm0
	vmovdqu YMMWORD PTR [rsp+1944], ymm0
	vmovdqu YMMWORD PTR [rsp+1912], ymm0
	vmovdqu YMMWORD PTR [rsp+1880], ymm0
	vmovdqu YMMWORD PTR [rsp+1848], ymm0
	vmovdqu YMMWORD PTR [rsp+1816], ymm0
	vmovdqu YMMWORD PTR [rsp+1784], ymm0
	vmovdqu YMMWORD PTR [rsp+1752], ymm0
	vmovdqu YMMWORD PTR [rsp+1720], ymm0
	vmovdqu YMMWORD PTR [rsp+1688], ymm0
	vmovdqu YMMWORD PTR [rsp+1656], ymm0
	vmovdqu YMMWORD PTR [rsp+1624], ymm0
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-376]
	mov QWORD PTR [rsp+368], r11
	vmovdqu YMMWORD PTR [rsp+336], ymm0
	vmovdqu YMMWORD PTR [rsp+304], ymm0
	vmovdqu YMMWORD PTR [rsp+272], ymm0
	vmovdqu YMMWORD PTR [rsp+240], ymm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+376]
	lea rsp, [rsp+4080]
	jmp 259f
258:
	xor r11d, r11d
	lea rsp, [rsp-4080]
	mov QWORD PTR [rsp+4072], r11
	vmovdqu YMMWORD PTR [rsp+4040], ymm0
	vmovdqu YMMWORD PTR [rsp+4008], ymm0
	vmovdqu YMMWORD PTR [rsp+3976], ymm0
	vmovdqu YMMWORD PTR [rsp+3944], ymm0
	vmovdqu YMMWORD PTR [rsp+3912], ymm0
	vmovdqu YMMWORD PTR [rsp+3880], ymm0
	vmovdqu YMMWORD PTR [rsp+3848], ymm0
	vmovdqu YMMWORD PTR [rsp+3816], ymm0
	vmovdqu YMMWORD PTR [rsp+3784], ymm0
	vmovdqu YMMWORD PTR [rsp+3752], ymm0
	vmovdqu YMMWORD PTR [rsp+3720], ymm0
	vmovdqu YMMWORD PTR [rsp+3688], ymm0
	vmovdqu YMMWORD PTR [rsp+3656], ymm0
	vmovdqu YMMWORD PTR [rsp+3624], ymm0
	vmovdqu YMMWORD PTR [rsp+3592], ymm0
	vmovdqu YMMWORD PTR [rsp+3560], ymm0
	vmovdqu YMMWORD PTR [rsp+3528], ymm0
	vmovdqu YMMWORD PTR [rsp+3496], ymm0
	vmovdqu YMMWORD PTR [rsp+3464], ymm0
	vmovdqu YMMWORD PTR [rsp+3432], ymm0
	vmovdqu YMMWORD PTR [rsp+3400], ymm0
	vmovdqu YMMWORD PTR [rsp+3368], ymm0
	vmovdqu YMMWORD PTR [rsp+3336], ymm0
	vmovdqu YMMWORD PTR [rsp+3304], ymm0
	vmovdqu YMMWORD PTR [rsp+3272], ymm0
	vmovdqu YMMWORD PTR [rsp+3240], ymm0
	vmovdqu YMMWORD PTR [rsp+3208], ymm0
	vmovdqu YMMWORD PTR [rsp+3176], ymm0
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
	vmovdqu YMMWORD PTR [rsp+3112], ymm0
	vmovdqu YMMWORD PTR [rsp+3080], ymm0
	vmovdqu YMMWORD PTR [rsp+3048], ymm0
	vmovdqu YMMWORD PTR [rsp+3016], ymm0
	vmovdqu YMMWORD PTR [rsp+2984], ymm0
	vmovdqu YMMWORD PTR [rsp+2952], ymm0
	vmovdqu YMMWORD PTR [rsp+2920], ymm0
	vmovdqu YMMWORD PTR [rsp+2888], ymm0
	vmovdqu YMMWORD PTR [rsp+2856], ymm0
	vmovdqu YMMWORD PTR [rsp+2824], ymm0
	vmovdqu YMMWORD PTR [rsp+2792], ymm0
	vmovdqu YMMWORD PTR [rsp+2760], ymm0
	vmovdqu YMMWORD PTR [rsp+2728], ymm0
	vmovdqu YMMWORD PTR [rsp+2696], ymm0
	vmovdqu YMMWORD PTR [rsp+2664], ymm0
	vmovdqu YMMWORD PTR [rsp+2632], ymm0
	vmovdqu YMMWORD PTR [rsp+2600], ymm0
	vmovdqu YMMWORD PTR [rsp+2568], ymm0
	vmovdqu YMMWORD PTR [rsp+2536], ymm0
	vmovdqu YMMWORD PTR [rsp+2504], ymm0
	vmovdqu YMMWORD PTR [rsp+2472], ymm0
	vmovdqu YMMWORD PTR [rsp+2440], ymm0
	vmovdqu YMMWORD PTR [rsp+2408], ymm0
	vmovdqu YMMWORD PTR [rsp+2376], ymm0
	vmovdqu YMMWORD PTR [rsp+2344], ymm0
	vmovdqu YMMWORD PTR [rsp+2312], ymm0
	vmovdqu YMMWORD PTR [rsp+2280], ymm0
	vmovdqu YMMWORD PTR [rsp+2248], ymm0
	vmovdqu YMMWORD PTR [rsp+2216], ymm0
	vmovdqu YMMWORD PTR [rsp+2184], ymm0
	vmovdqu YMMWORD PTR [rsp+2152], ymm0
	vmovdqu YMMWORD PTR [rsp+2120], ymm0
	vmovdqu YMMWORD PTR [rsp+2088], ymm0
	vmovdqu YMMWORD PTR [rsp+2056], ymm0
	vmovdqu YMMWORD PTR [rsp+2024], ymm0
	vmovdqu YMMWORD PTR [rsp+1992], ymm0
	vmovdqu YMMWORD PTR [rsp+1960], ymm0
	vmovdqu YMMWORD PTR [rsp+1928], ymm0
	vmovdqu YMMWORD PTR [rsp+1896], ymm0
	vmovdqu YMMWORD PTR [rsp+1864], ymm0
	vmovdqu YMMWORD PTR [rsp+1832], ymm0
	vmovdqu YMMWORD PTR [rsp+1800], ymm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-376]
	mov QWORD PTR [rsp+368], r11
	movdqu XMMWORD PTR [rsp+352], xmm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+376]
	lea rsp, [rsp+4080]
259:
	mov eax, eax
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

vg_rsa_pkcs1_sign_precomputed:
	lea rsp, [rsp-1192]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rsi
	mov QWORD PTR [rsp+128], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+144], r8
	mov QWORD PTR [rsp+152], r9
	mov r8, rsp
	add r8, 160
	mov rdx, QWORD PTR [rsp+1200]
	mov edx, edx
	mov rsi, QWORD PTR [rsp+1208]
	mov r9, QWORD PTR [rsp+1216]
	cmp edx, 0
	je 20f
	cmp edx, 1
	je 22f
	cmp edx, 2
	je 24f
	cmp edx, 3
	je 26f
	cmp edx, 4
	je 28f
	cmp edx, 5
	je 210f
	cmp edx, 6
	je 212f
	cmp edx, 7
	je 214f
	cmp edx, 8
	je 216f
	cmp edx, 9
	je 218f
	cmp edx, 10
	je 220f
	cmp edx, 11
	je 222f
	mov r10d, 2048
	mov r11d, 0
	jmp 223f
222:
	mov r10d, 83
	mov r11d, 64
223:
	jmp 221f
220:
	mov r10d, 67
	mov r11d, 48
221:
	jmp 219f
218:
	mov r10d, 51
	mov r11d, 32
219:
	jmp 217f
216:
	mov r10d, 47
	mov r11d, 28
217:
	jmp 215f
214:
	mov r10d, 51
	mov r11d, 32
215:
	jmp 213f
212:
	mov r10d, 47
	mov r11d, 28
213:
	jmp 211f
210:
	mov r10d, 83
	mov r11d, 64
211:
	jmp 29f
28:
	mov r10d, 67
	mov r11d, 48
29:
	jmp 27f
26:
	mov r10d, 51
	mov r11d, 32
27:
	jmp 25f
24:
	mov r10d, 47
	mov r11d, 28
25:
	jmp 23f
22:
	mov r10d, 35
	mov r11d, 20
23:
	jmp 21f
20:
	mov r10d, 34
	mov r11d, 16
21:
	cmp r9, r11
	jne 224f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 226f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
228:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 228b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 229f
	cmp edx, 1
	je 231f
	cmp edx, 2
	je 233f
	cmp edx, 3
	je 235f
	cmp edx, 4
	je 237f
	cmp edx, 5
	je 239f
	cmp edx, 6
	je 241f
	cmp edx, 7
	je 243f
	cmp edx, 8
	je 245f
	cmp edx, 9
	je 247f
	cmp edx, 10
	je 249f
	cmp edx, 11
	je 251f
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
232:
	jmp 230f
229:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
230:
253:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 253b
	mov eax, 1
	jmp 227f
226:
	mov eax, 0
227:
	jmp 225f
224:
	mov eax, 0
225:
	cmp eax, 0
	je 254f
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+120]
	mov rdx, QWORD PTR [rsp+128]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+144]
	mov r9, QWORD PTR [rsp+152]
	mov rax, rsp
	add rax, 160
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rcx
	mov rax, QWORD PTR [rsp+1224]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+1232]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+1240]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+1248]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+1256]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+1264]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+1272]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+1280]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+1288]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+1296]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+1304]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+1312]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rsp+1320]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+1328]
	mov QWORD PTR [rsp+120], rax
	call {vg_rsa_private_checked_precomputed}
	mov r11, QWORD PTR [rsp+136]
	mov edx, 0
	mov r10, rsp
	add r10, 160
256:
	mov BYTE PTR [r10], dl
	add r10, 1
	sub r11, 1
	jne 256b
	jmp 255f
254:
	mov rdi, QWORD PTR [rsp+112]
	mov rsi, QWORD PTR [rsp+120]
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
257:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 257b
255:
	lea rsp, [rsp+1192]
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
	lea rsp, [rsp-4080]
	mov QWORD PTR [rsp+4072], r11
	movdqu XMMWORD PTR [rsp+4056], xmm0
	movdqu XMMWORD PTR [rsp+4040], xmm0
	movdqu XMMWORD PTR [rsp+4024], xmm0
	movdqu XMMWORD PTR [rsp+4008], xmm0
	movdqu XMMWORD PTR [rsp+3992], xmm0
	movdqu XMMWORD PTR [rsp+3976], xmm0
	movdqu XMMWORD PTR [rsp+3960], xmm0
	movdqu XMMWORD PTR [rsp+3944], xmm0
	movdqu XMMWORD PTR [rsp+3928], xmm0
	movdqu XMMWORD PTR [rsp+3912], xmm0
	movdqu XMMWORD PTR [rsp+3896], xmm0
	movdqu XMMWORD PTR [rsp+3880], xmm0
	movdqu XMMWORD PTR [rsp+3864], xmm0
	movdqu XMMWORD PTR [rsp+3848], xmm0
	movdqu XMMWORD PTR [rsp+3832], xmm0
	movdqu XMMWORD PTR [rsp+3816], xmm0
	movdqu XMMWORD PTR [rsp+3800], xmm0
	movdqu XMMWORD PTR [rsp+3784], xmm0
	movdqu XMMWORD PTR [rsp+3768], xmm0
	movdqu XMMWORD PTR [rsp+3752], xmm0
	movdqu XMMWORD PTR [rsp+3736], xmm0
	movdqu XMMWORD PTR [rsp+3720], xmm0
	movdqu XMMWORD PTR [rsp+3704], xmm0
	movdqu XMMWORD PTR [rsp+3688], xmm0
	movdqu XMMWORD PTR [rsp+3672], xmm0
	movdqu XMMWORD PTR [rsp+3656], xmm0
	movdqu XMMWORD PTR [rsp+3640], xmm0
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-376]
	mov QWORD PTR [rsp+368], r11
	movdqu XMMWORD PTR [rsp+352], xmm0
	movdqu XMMWORD PTR [rsp+336], xmm0
	movdqu XMMWORD PTR [rsp+320], xmm0
	movdqu XMMWORD PTR [rsp+304], xmm0
	movdqu XMMWORD PTR [rsp+288], xmm0
	movdqu XMMWORD PTR [rsp+272], xmm0
	movdqu XMMWORD PTR [rsp+256], xmm0
	movdqu XMMWORD PTR [rsp+240], xmm0
	movdqu XMMWORD PTR [rsp+224], xmm0
	movdqu XMMWORD PTR [rsp+208], xmm0
	movdqu XMMWORD PTR [rsp+192], xmm0
	movdqu XMMWORD PTR [rsp+176], xmm0
	movdqu XMMWORD PTR [rsp+160], xmm0
	movdqu XMMWORD PTR [rsp+144], xmm0
	movdqu XMMWORD PTR [rsp+128], xmm0
	movdqu XMMWORD PTR [rsp+112], xmm0
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+376]
	lea rsp, [rsp+4080]
	mov eax, eax
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

vg_rsa_pkcs1_verify_precomputed_ifma:
	mov rax, QWORD PTR [rsp+24]
	cmp rax, rsi
	jne 20f
	lea rsp, [rsp-2136]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rsi
	mov QWORD PTR [rsp+48], rdx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], r8
	mov QWORD PTR [rsp+72], r9
	mov rax, QWORD PTR [rsp+2152]
	mov r10, QWORD PTR [rsp+2168]
	mov r11, QWORD PTR [rsp+2176]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rsi
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, rdx
	mov r9, rcx
	mov rdx, rdi
	mov rcx, rsi
	mov rdi, rsp
	add rdi, 80
	mov rdx, QWORD PTR [rsp+2184]
	mov rcx, QWORD PTR [rsp+2192]
	call {vg_rsa_public_precomputed_checked_ifma}
	mov QWORD PTR [rsp], rax
	mov eax, 1
	cmp eax, 0
	je 22f
	mov r8, rsp
	add r8, 1104
	mov rcx, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+64]
	mov edx, edx
	mov rsi, QWORD PTR [rsp+72]
	mov r9, QWORD PTR [rsp+2144]
	cmp edx, 0
	je 24f
	cmp edx, 1
	je 26f
	cmp edx, 2
	je 28f
	cmp edx, 3
	je 210f
	cmp edx, 4
	je 212f
	cmp edx, 5
	je 214f
	cmp edx, 6
	je 216f
	cmp edx, 7
	je 218f
	cmp edx, 8
	je 220f
	cmp edx, 9
	je 222f
	cmp edx, 10
	je 224f
	cmp edx, 11
	je 226f
	mov r10d, 2048
	mov r11d, 0
	jmp 227f
226:
	mov r10d, 83
	mov r11d, 64
227:
	jmp 225f
224:
	mov r10d, 67
	mov r11d, 48
225:
	jmp 223f
222:
	mov r10d, 51
	mov r11d, 32
223:
	jmp 221f
220:
	mov r10d, 47
	mov r11d, 28
221:
	jmp 219f
218:
	mov r10d, 51
	mov r11d, 32
219:
	jmp 217f
216:
	mov r10d, 47
	mov r11d, 28
217:
	jmp 215f
214:
	mov r10d, 83
	mov r11d, 64
215:
	jmp 213f
212:
	mov r10d, 67
	mov r11d, 48
213:
	jmp 211f
210:
	mov r10d, 51
	mov r11d, 32
211:
	jmp 29f
28:
	mov r10d, 47
	mov r11d, 28
29:
	jmp 27f
26:
	mov r10d, 35
	mov r11d, 20
27:
	jmp 25f
24:
	mov r10d, 34
	mov r11d, 16
25:
	cmp r9, r11
	jne 228f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 230f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
232:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 232b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 233f
	cmp edx, 1
	je 235f
	cmp edx, 2
	je 237f
	cmp edx, 3
	je 239f
	cmp edx, 4
	je 241f
	cmp edx, 5
	je 243f
	cmp edx, 6
	je 245f
	cmp edx, 7
	je 247f
	cmp edx, 8
	je 249f
	cmp edx, 9
	je 251f
	cmp edx, 10
	je 253f
	cmp edx, 11
	je 255f
	jmp 256f
255:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
256:
	jmp 254f
253:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
254:
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
257:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 257b
	mov eax, 1
	jmp 231f
230:
	mov eax, 0
231:
	jmp 229f
228:
	mov eax, 0
229:
	cmp eax, 0
	je 258f
	mov rdi, rsp
	add rdi, 80
	mov rsi, rsp
	add rsi, 1104
	mov r11d, 0
	mov edx, 0
	mov rax, rcx
	and rax, 7
	je 260f
262:
	movzx eax, BYTE PTR [rdi+r11*1]
	movzx r10d, BYTE PTR [rsi+r11*1]
	xor rax, r10
	or rdx, rax
	add r11, 1
	cmp r11, rcx
	jne 262b
	jmp 261f
260:
263:
	mov rax, QWORD PTR [rdi+r11*1]
	xor rax, QWORD PTR [rsi+r11*1]
	or rdx, rax
	add r11, 8
	cmp r11, rcx
	jne 263b
261:
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 259f
258:
	mov eax, 0
259:
	jmp 23f
22:
	mov eax, 0
23:
	mov rcx, QWORD PTR [rsp]
	and eax, ecx
	lea rsp, [rsp+2136]
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6

vg_rsa_pkcs1_recover_precomputed_ifma:
	mov rax, QWORD PTR [rsp+24]
	cmp rax, rcx
	jne 20f
	lea rsp, [rsp-2136]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rsi
	mov QWORD PTR [rsp+48], rdx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], r8
	mov QWORD PTR [rsp+72], r9
	mov rax, QWORD PTR [rsp+2152]
	mov r10, QWORD PTR [rsp+2168]
	mov r11, QWORD PTR [rsp+2176]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov rsi, rcx
	mov rdi, rsp
	add rdi, 80
	mov rdx, QWORD PTR [rsp+2184]
	mov rcx, QWORD PTR [rsp+2192]
	call {vg_rsa_public_precomputed_checked_ifma}
	mov QWORD PTR [rsp], rax
	mov r8, rsp
	add r8, 1104
	mov rcx, QWORD PTR [rsp+56]
	mov rdx, QWORD PTR [rsp+2144]
	mov edx, edx
	mov r9, QWORD PTR [rsp+40]
	mov rsi, rsp
	add rsi, 80
	add rsi, rcx
	sub rsi, r9
	cmp edx, 0
	je 22f
	cmp edx, 1
	je 24f
	cmp edx, 2
	je 26f
	cmp edx, 3
	je 28f
	cmp edx, 4
	je 210f
	cmp edx, 5
	je 212f
	cmp edx, 6
	je 214f
	cmp edx, 7
	je 216f
	cmp edx, 8
	je 218f
	cmp edx, 9
	je 220f
	cmp edx, 10
	je 222f
	cmp edx, 11
	je 224f
	mov r10d, 2048
	mov r11d, 0
	jmp 225f
224:
	mov r10d, 83
	mov r11d, 64
225:
	jmp 223f
222:
	mov r10d, 67
	mov r11d, 48
223:
	jmp 221f
220:
	mov r10d, 51
	mov r11d, 32
221:
	jmp 219f
218:
	mov r10d, 47
	mov r11d, 28
219:
	jmp 217f
216:
	mov r10d, 51
	mov r11d, 32
217:
	jmp 215f
214:
	mov r10d, 47
	mov r11d, 28
215:
	jmp 213f
212:
	mov r10d, 83
	mov r11d, 64
213:
	jmp 211f
210:
	mov r10d, 67
	mov r11d, 48
211:
	jmp 29f
28:
	mov r10d, 51
	mov r11d, 32
29:
	jmp 27f
26:
	mov r10d, 47
	mov r11d, 28
27:
	jmp 25f
24:
	mov r10d, 35
	mov r11d, 20
25:
	jmp 23f
22:
	mov r10d, 34
	mov r11d, 16
23:
	cmp r9, r11
	jne 226f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 228f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
230:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 230b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 231f
	cmp edx, 1
	je 233f
	cmp edx, 2
	je 235f
	cmp edx, 3
	je 237f
	cmp edx, 4
	je 239f
	cmp edx, 5
	je 241f
	cmp edx, 6
	je 243f
	cmp edx, 7
	je 245f
	cmp edx, 8
	je 247f
	cmp edx, 9
	je 249f
	cmp edx, 10
	je 251f
	cmp edx, 11
	je 253f
	jmp 254f
253:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
254:
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
232:
255:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 255b
	mov eax, 1
	jmp 229f
228:
	mov eax, 0
229:
	jmp 227f
226:
	mov eax, 0
227:
	cmp eax, 0
	je 256f
	mov rdi, rsp
	add rdi, 80
	mov rsi, rsp
	add rsi, 1104
	mov r11d, 0
	mov edx, 0
	mov rax, rcx
	and rax, 7
	je 258f
260:
	movzx eax, BYTE PTR [rdi+r11*1]
	movzx r10d, BYTE PTR [rsi+r11*1]
	xor rax, r10
	or rdx, rax
	add r11, 1
	cmp r11, rcx
	jne 260b
	jmp 259f
258:
261:
	mov rax, QWORD PTR [rdi+r11*1]
	xor rax, QWORD PTR [rsi+r11*1]
	or rdx, rax
	add r11, 8
	cmp r11, rcx
	jne 261b
259:
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp]
	cmp eax, 1
	sbb rax, rax
	xor rax, -1
	and rdx, rax
	mov QWORD PTR [rsp+8], rdx
	mov r8, QWORD PTR [rsp+32]
	mov rdi, r8
	mov r9, QWORD PTR [rsp+40]
	mov rsi, rsp
	add rsi, 80
	add rsi, rcx
	sub rsi, r9
262:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 262b
	mov eax, 1
	mov rdi, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+8]
	mov r10d, 0
263:
	movzx eax, BYTE PTR [rdi+r10*1]
	and rax, rdx
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+80], al
	add r10, 1
	cmp r10, rcx
	jne 263b
	mov rax, rdx
	and rax, 1
	jmp 257f
256:
	mov rdi, QWORD PTR [rsp+32]
	mov rsi, QWORD PTR [rsp+40]
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
264:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 264b
257:
	lea rsp, [rsp+2136]
	jmp 21f
20:
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
265:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 265b
21:
	ret
	.p2align 6

vg_rsa_pkcs1_verify_precomputed_adx:
	mov rax, QWORD PTR [rsp+24]
	cmp rax, rsi
	jne 20f
	lea rsp, [rsp-2136]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rsi
	mov QWORD PTR [rsp+48], rdx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], r8
	mov QWORD PTR [rsp+72], r9
	mov rax, QWORD PTR [rsp+2152]
	mov r10, QWORD PTR [rsp+2168]
	mov r11, QWORD PTR [rsp+2176]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rsi
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, rdx
	mov r9, rcx
	mov rdx, rdi
	mov rcx, rsi
	mov rdi, rsp
	add rdi, 80
	mov rdx, QWORD PTR [rsp+2184]
	mov rcx, QWORD PTR [rsp+2192]
	call {vg_rsa_public_precomputed_checked_adx}
	mov QWORD PTR [rsp], rax
	mov eax, 1
	cmp eax, 0
	je 22f
	mov r8, rsp
	add r8, 1104
	mov rcx, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+64]
	mov edx, edx
	mov rsi, QWORD PTR [rsp+72]
	mov r9, QWORD PTR [rsp+2144]
	cmp edx, 0
	je 24f
	cmp edx, 1
	je 26f
	cmp edx, 2
	je 28f
	cmp edx, 3
	je 210f
	cmp edx, 4
	je 212f
	cmp edx, 5
	je 214f
	cmp edx, 6
	je 216f
	cmp edx, 7
	je 218f
	cmp edx, 8
	je 220f
	cmp edx, 9
	je 222f
	cmp edx, 10
	je 224f
	cmp edx, 11
	je 226f
	mov r10d, 2048
	mov r11d, 0
	jmp 227f
226:
	mov r10d, 83
	mov r11d, 64
227:
	jmp 225f
224:
	mov r10d, 67
	mov r11d, 48
225:
	jmp 223f
222:
	mov r10d, 51
	mov r11d, 32
223:
	jmp 221f
220:
	mov r10d, 47
	mov r11d, 28
221:
	jmp 219f
218:
	mov r10d, 51
	mov r11d, 32
219:
	jmp 217f
216:
	mov r10d, 47
	mov r11d, 28
217:
	jmp 215f
214:
	mov r10d, 83
	mov r11d, 64
215:
	jmp 213f
212:
	mov r10d, 67
	mov r11d, 48
213:
	jmp 211f
210:
	mov r10d, 51
	mov r11d, 32
211:
	jmp 29f
28:
	mov r10d, 47
	mov r11d, 28
29:
	jmp 27f
26:
	mov r10d, 35
	mov r11d, 20
27:
	jmp 25f
24:
	mov r10d, 34
	mov r11d, 16
25:
	cmp r9, r11
	jne 228f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 230f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
232:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 232b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 233f
	cmp edx, 1
	je 235f
	cmp edx, 2
	je 237f
	cmp edx, 3
	je 239f
	cmp edx, 4
	je 241f
	cmp edx, 5
	je 243f
	cmp edx, 6
	je 245f
	cmp edx, 7
	je 247f
	cmp edx, 8
	je 249f
	cmp edx, 9
	je 251f
	cmp edx, 10
	je 253f
	cmp edx, 11
	je 255f
	jmp 256f
255:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
256:
	jmp 254f
253:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
254:
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
257:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 257b
	mov eax, 1
	jmp 231f
230:
	mov eax, 0
231:
	jmp 229f
228:
	mov eax, 0
229:
	cmp eax, 0
	je 258f
	mov rdi, rsp
	add rdi, 80
	mov rsi, rsp
	add rsi, 1104
	mov r11d, 0
	mov edx, 0
	mov rax, rcx
	and rax, 7
	je 260f
262:
	movzx eax, BYTE PTR [rdi+r11*1]
	movzx r10d, BYTE PTR [rsi+r11*1]
	xor rax, r10
	or rdx, rax
	add r11, 1
	cmp r11, rcx
	jne 262b
	jmp 261f
260:
263:
	mov rax, QWORD PTR [rdi+r11*1]
	xor rax, QWORD PTR [rsi+r11*1]
	or rdx, rax
	add r11, 8
	cmp r11, rcx
	jne 263b
261:
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 259f
258:
	mov eax, 0
259:
	jmp 23f
22:
	mov eax, 0
23:
	mov rcx, QWORD PTR [rsp]
	and eax, ecx
	lea rsp, [rsp+2136]
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6

vg_rsa_pkcs1_recover_precomputed_adx:
	mov rax, QWORD PTR [rsp+24]
	cmp rax, rcx
	jne 20f
	lea rsp, [rsp-2136]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rsi
	mov QWORD PTR [rsp+48], rdx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], r8
	mov QWORD PTR [rsp+72], r9
	mov rax, QWORD PTR [rsp+2152]
	mov r10, QWORD PTR [rsp+2168]
	mov r11, QWORD PTR [rsp+2176]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov rsi, rcx
	mov rdi, rsp
	add rdi, 80
	mov rdx, QWORD PTR [rsp+2184]
	mov rcx, QWORD PTR [rsp+2192]
	call {vg_rsa_public_precomputed_checked_adx}
	mov QWORD PTR [rsp], rax
	mov r8, rsp
	add r8, 1104
	mov rcx, QWORD PTR [rsp+56]
	mov rdx, QWORD PTR [rsp+2144]
	mov edx, edx
	mov r9, QWORD PTR [rsp+40]
	mov rsi, rsp
	add rsi, 80
	add rsi, rcx
	sub rsi, r9
	cmp edx, 0
	je 22f
	cmp edx, 1
	je 24f
	cmp edx, 2
	je 26f
	cmp edx, 3
	je 28f
	cmp edx, 4
	je 210f
	cmp edx, 5
	je 212f
	cmp edx, 6
	je 214f
	cmp edx, 7
	je 216f
	cmp edx, 8
	je 218f
	cmp edx, 9
	je 220f
	cmp edx, 10
	je 222f
	cmp edx, 11
	je 224f
	mov r10d, 2048
	mov r11d, 0
	jmp 225f
224:
	mov r10d, 83
	mov r11d, 64
225:
	jmp 223f
222:
	mov r10d, 67
	mov r11d, 48
223:
	jmp 221f
220:
	mov r10d, 51
	mov r11d, 32
221:
	jmp 219f
218:
	mov r10d, 47
	mov r11d, 28
219:
	jmp 217f
216:
	mov r10d, 51
	mov r11d, 32
217:
	jmp 215f
214:
	mov r10d, 47
	mov r11d, 28
215:
	jmp 213f
212:
	mov r10d, 83
	mov r11d, 64
213:
	jmp 211f
210:
	mov r10d, 67
	mov r11d, 48
211:
	jmp 29f
28:
	mov r10d, 51
	mov r11d, 32
29:
	jmp 27f
26:
	mov r10d, 47
	mov r11d, 28
27:
	jmp 25f
24:
	mov r10d, 35
	mov r11d, 20
25:
	jmp 23f
22:
	mov r10d, 34
	mov r11d, 16
23:
	cmp r9, r11
	jne 226f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 228f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
230:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 230b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 231f
	cmp edx, 1
	je 233f
	cmp edx, 2
	je 235f
	cmp edx, 3
	je 237f
	cmp edx, 4
	je 239f
	cmp edx, 5
	je 241f
	cmp edx, 6
	je 243f
	cmp edx, 7
	je 245f
	cmp edx, 8
	je 247f
	cmp edx, 9
	je 249f
	cmp edx, 10
	je 251f
	cmp edx, 11
	je 253f
	jmp 254f
253:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
254:
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
232:
255:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 255b
	mov eax, 1
	jmp 229f
228:
	mov eax, 0
229:
	jmp 227f
226:
	mov eax, 0
227:
	cmp eax, 0
	je 256f
	mov rdi, rsp
	add rdi, 80
	mov rsi, rsp
	add rsi, 1104
	mov r11d, 0
	mov edx, 0
	mov rax, rcx
	and rax, 7
	je 258f
260:
	movzx eax, BYTE PTR [rdi+r11*1]
	movzx r10d, BYTE PTR [rsi+r11*1]
	xor rax, r10
	or rdx, rax
	add r11, 1
	cmp r11, rcx
	jne 260b
	jmp 259f
258:
261:
	mov rax, QWORD PTR [rdi+r11*1]
	xor rax, QWORD PTR [rsi+r11*1]
	or rdx, rax
	add r11, 8
	cmp r11, rcx
	jne 261b
259:
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp]
	cmp eax, 1
	sbb rax, rax
	xor rax, -1
	and rdx, rax
	mov QWORD PTR [rsp+8], rdx
	mov r8, QWORD PTR [rsp+32]
	mov rdi, r8
	mov r9, QWORD PTR [rsp+40]
	mov rsi, rsp
	add rsi, 80
	add rsi, rcx
	sub rsi, r9
262:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 262b
	mov eax, 1
	mov rdi, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+8]
	mov r10d, 0
263:
	movzx eax, BYTE PTR [rdi+r10*1]
	and rax, rdx
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+80], al
	add r10, 1
	cmp r10, rcx
	jne 263b
	mov rax, rdx
	and rax, 1
	jmp 257f
256:
	mov rdi, QWORD PTR [rsp+32]
	mov rsi, QWORD PTR [rsp+40]
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
264:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 264b
257:
	lea rsp, [rsp+2136]
	jmp 21f
20:
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
265:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 265b
21:
	ret
	.p2align 6

vg_rsa_pkcs1_verify_precomputed:
	mov rax, QWORD PTR [rsp+24]
	cmp rax, rsi
	jne 20f
	lea rsp, [rsp-2136]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rsi
	mov QWORD PTR [rsp+48], rdx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], r8
	mov QWORD PTR [rsp+72], r9
	mov rax, QWORD PTR [rsp+2152]
	mov r10, QWORD PTR [rsp+2168]
	mov r11, QWORD PTR [rsp+2176]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rsi
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, rdx
	mov r9, rcx
	mov rdx, rdi
	mov rcx, rsi
	mov rdi, rsp
	add rdi, 80
	mov rdx, QWORD PTR [rsp+2184]
	mov rcx, QWORD PTR [rsp+2192]
	call {vg_rsa_public_precomputed_checked}
	mov QWORD PTR [rsp], rax
	mov eax, 1
	cmp eax, 0
	je 22f
	mov r8, rsp
	add r8, 1104
	mov rcx, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+64]
	mov edx, edx
	mov rsi, QWORD PTR [rsp+72]
	mov r9, QWORD PTR [rsp+2144]
	cmp edx, 0
	je 24f
	cmp edx, 1
	je 26f
	cmp edx, 2
	je 28f
	cmp edx, 3
	je 210f
	cmp edx, 4
	je 212f
	cmp edx, 5
	je 214f
	cmp edx, 6
	je 216f
	cmp edx, 7
	je 218f
	cmp edx, 8
	je 220f
	cmp edx, 9
	je 222f
	cmp edx, 10
	je 224f
	cmp edx, 11
	je 226f
	mov r10d, 2048
	mov r11d, 0
	jmp 227f
226:
	mov r10d, 83
	mov r11d, 64
227:
	jmp 225f
224:
	mov r10d, 67
	mov r11d, 48
225:
	jmp 223f
222:
	mov r10d, 51
	mov r11d, 32
223:
	jmp 221f
220:
	mov r10d, 47
	mov r11d, 28
221:
	jmp 219f
218:
	mov r10d, 51
	mov r11d, 32
219:
	jmp 217f
216:
	mov r10d, 47
	mov r11d, 28
217:
	jmp 215f
214:
	mov r10d, 83
	mov r11d, 64
215:
	jmp 213f
212:
	mov r10d, 67
	mov r11d, 48
213:
	jmp 211f
210:
	mov r10d, 51
	mov r11d, 32
211:
	jmp 29f
28:
	mov r10d, 47
	mov r11d, 28
29:
	jmp 27f
26:
	mov r10d, 35
	mov r11d, 20
27:
	jmp 25f
24:
	mov r10d, 34
	mov r11d, 16
25:
	cmp r9, r11
	jne 228f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 230f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
232:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 232b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 233f
	cmp edx, 1
	je 235f
	cmp edx, 2
	je 237f
	cmp edx, 3
	je 239f
	cmp edx, 4
	je 241f
	cmp edx, 5
	je 243f
	cmp edx, 6
	je 245f
	cmp edx, 7
	je 247f
	cmp edx, 8
	je 249f
	cmp edx, 9
	je 251f
	cmp edx, 10
	je 253f
	cmp edx, 11
	je 255f
	jmp 256f
255:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
256:
	jmp 254f
253:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
254:
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
257:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 257b
	mov eax, 1
	jmp 231f
230:
	mov eax, 0
231:
	jmp 229f
228:
	mov eax, 0
229:
	cmp eax, 0
	je 258f
	mov rdi, rsp
	add rdi, 80
	mov rsi, rsp
	add rsi, 1104
	mov r11d, 0
	mov edx, 0
	mov rax, rcx
	and rax, 7
	je 260f
262:
	movzx eax, BYTE PTR [rdi+r11*1]
	movzx r10d, BYTE PTR [rsi+r11*1]
	xor rax, r10
	or rdx, rax
	add r11, 1
	cmp r11, rcx
	jne 262b
	jmp 261f
260:
263:
	mov rax, QWORD PTR [rdi+r11*1]
	xor rax, QWORD PTR [rsi+r11*1]
	or rdx, rax
	add r11, 8
	cmp r11, rcx
	jne 263b
261:
	cmp rdx, 1
	sbb rax, rax
	and rax, 1
	jmp 259f
258:
	mov eax, 0
259:
	jmp 23f
22:
	mov eax, 0
23:
	mov rcx, QWORD PTR [rsp]
	and eax, ecx
	lea rsp, [rsp+2136]
	jmp 21f
20:
	mov eax, 0
21:
	ret
	.p2align 6

vg_rsa_pkcs1_recover_precomputed:
	mov rax, QWORD PTR [rsp+24]
	cmp rax, rcx
	jne 20f
	lea rsp, [rsp-2136]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rsi
	mov QWORD PTR [rsp+48], rdx
	mov QWORD PTR [rsp+56], rcx
	mov QWORD PTR [rsp+64], r8
	mov QWORD PTR [rsp+72], r9
	mov rax, QWORD PTR [rsp+2152]
	mov r10, QWORD PTR [rsp+2168]
	mov r11, QWORD PTR [rsp+2176]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov rsi, rcx
	mov rdi, rsp
	add rdi, 80
	mov rdx, QWORD PTR [rsp+2184]
	mov rcx, QWORD PTR [rsp+2192]
	call {vg_rsa_public_precomputed_checked}
	mov QWORD PTR [rsp], rax
	mov r8, rsp
	add r8, 1104
	mov rcx, QWORD PTR [rsp+56]
	mov rdx, QWORD PTR [rsp+2144]
	mov edx, edx
	mov r9, QWORD PTR [rsp+40]
	mov rsi, rsp
	add rsi, 80
	add rsi, rcx
	sub rsi, r9
	cmp edx, 0
	je 22f
	cmp edx, 1
	je 24f
	cmp edx, 2
	je 26f
	cmp edx, 3
	je 28f
	cmp edx, 4
	je 210f
	cmp edx, 5
	je 212f
	cmp edx, 6
	je 214f
	cmp edx, 7
	je 216f
	cmp edx, 8
	je 218f
	cmp edx, 9
	je 220f
	cmp edx, 10
	je 222f
	cmp edx, 11
	je 224f
	mov r10d, 2048
	mov r11d, 0
	jmp 225f
224:
	mov r10d, 83
	mov r11d, 64
225:
	jmp 223f
222:
	mov r10d, 67
	mov r11d, 48
223:
	jmp 221f
220:
	mov r10d, 51
	mov r11d, 32
221:
	jmp 219f
218:
	mov r10d, 47
	mov r11d, 28
219:
	jmp 217f
216:
	mov r10d, 51
	mov r11d, 32
217:
	jmp 215f
214:
	mov r10d, 47
	mov r11d, 28
215:
	jmp 213f
212:
	mov r10d, 83
	mov r11d, 64
213:
	jmp 211f
210:
	mov r10d, 67
	mov r11d, 48
211:
	jmp 29f
28:
	mov r10d, 51
	mov r11d, 32
29:
	jmp 27f
26:
	mov r10d, 47
	mov r11d, 28
27:
	jmp 25f
24:
	mov r10d, 35
	mov r11d, 20
25:
	jmp 23f
22:
	mov r10d, 34
	mov r11d, 16
23:
	cmp r9, r11
	jne 226f
	mov rax, r10
	add rax, 11
	cmp rcx, rax
	jb 228f
	mov rdi, r8
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov rax, rcx
	sub rax, r10
	sub rax, 3
	mov r10, rax
	mov eax, 255
230:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 230b
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	cmp edx, 0
	je 231f
	cmp edx, 1
	je 233f
	cmp edx, 2
	je 235f
	cmp edx, 3
	je 237f
	cmp edx, 4
	je 239f
	cmp edx, 5
	je 241f
	cmp edx, 6
	je 243f
	cmp edx, 7
	je 245f
	cmp edx, 8
	je 247f
	cmp edx, 9
	je 249f
	cmp edx, 10
	je 251f
	cmp edx, 11
	je 253f
	jmp 254f
253:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 10
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
254:
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 7
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 81
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 64
	mov BYTE PTR [rdi], al
	add rdi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 65
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 49
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 45
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 96
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 101
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 28
	mov BYTE PTR [rdi], al
	add rdi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 33
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 9
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 43
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 14
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 3
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 26
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 20
	mov BYTE PTR [rdi], al
	add rdi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 32
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 48
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 12
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 6
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 8
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 42
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 72
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 134
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 247
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 13
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 2
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 5
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 4
	mov BYTE PTR [rdi], al
	add rdi, 1
	mov eax, 16
	mov BYTE PTR [rdi], al
	add rdi, 1
232:
255:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 255b
	mov eax, 1
	jmp 229f
228:
	mov eax, 0
229:
	jmp 227f
226:
	mov eax, 0
227:
	cmp eax, 0
	je 256f
	mov rdi, rsp
	add rdi, 80
	mov rsi, rsp
	add rsi, 1104
	mov r11d, 0
	mov edx, 0
	mov rax, rcx
	and rax, 7
	je 258f
260:
	movzx eax, BYTE PTR [rdi+r11*1]
	movzx r10d, BYTE PTR [rsi+r11*1]
	xor rax, r10
	or rdx, rax
	add r11, 1
	cmp r11, rcx
	jne 260b
	jmp 259f
258:
261:
	mov rax, QWORD PTR [rdi+r11*1]
	xor rax, QWORD PTR [rsi+r11*1]
	or rdx, rax
	add r11, 8
	cmp r11, rcx
	jne 261b
259:
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rsp]
	cmp eax, 1
	sbb rax, rax
	xor rax, -1
	and rdx, rax
	mov QWORD PTR [rsp+8], rdx
	mov r8, QWORD PTR [rsp+32]
	mov rdi, r8
	mov r9, QWORD PTR [rsp+40]
	mov rsi, rsp
	add rsi, 80
	add rsi, rcx
	sub rsi, r9
262:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [rdi], al
	add rsi, 1
	add rdi, 1
	sub r9, 1
	jne 262b
	mov eax, 1
	mov rdi, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+8]
	mov r10d, 0
263:
	movzx eax, BYTE PTR [rdi+r10*1]
	and rax, rdx
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+80], al
	add r10, 1
	cmp r10, rcx
	jne 263b
	mov rax, rdx
	and rax, 1
	jmp 257f
256:
	mov rdi, QWORD PTR [rsp+32]
	mov rsi, QWORD PTR [rsp+40]
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
264:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 264b
257:
	lea rsp, [rsp+2136]
	jmp 21f
20:
	mov r8, rdi
	mov r10, rsi
	mov eax, 0
265:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 265b
21:
	ret
	.p2align 6
