// The functions of `src/rsa_pkcs1_sig.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_sign_adx:
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
	call {vg_rsa_private_checked_adx}
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
	ret
	.p2align 6

vg_rsa_pkcs1_sign:
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
	call {vg_rsa_private_checked}
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
	ret
	.p2align 6

vg_rsa_pkcs1_sign_ifma:
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
	call {vg_rsa_private_checked_ifma}
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
