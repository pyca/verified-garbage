// The functions of `src/rsa_pkcs1_sig.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_verify_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-2112]
	mov eax, DWORD PTR [esp+2164]
	cmp eax, DWORD PTR [esp+2136]
	jne 20f
	mov eax, esp
	add eax, 64
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+2136]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2140]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2144]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2160]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2136]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2168]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2172]
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov DWORD PTR [esp+40], eax
	mov edi, esp
	add edi, 1088
	mov ecx, DWORD PTR [esp+2136]
	mov edx, DWORD PTR [esp+2148]
	mov esi, DWORD PTR [esp+2152]
	mov ebp, DWORD PTR [esp+2156]
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
	mov ebx, 2048
	mov eax, 0
	jmp 225f
224:
	mov ebx, 83
	mov eax, 64
225:
	jmp 223f
222:
	mov ebx, 67
	mov eax, 48
223:
	jmp 221f
220:
	mov ebx, 51
	mov eax, 32
221:
	jmp 219f
218:
	mov ebx, 47
	mov eax, 28
219:
	jmp 217f
216:
	mov ebx, 51
	mov eax, 32
217:
	jmp 215f
214:
	mov ebx, 47
	mov eax, 28
215:
	jmp 213f
212:
	mov ebx, 83
	mov eax, 64
213:
	jmp 211f
210:
	mov ebx, 67
	mov eax, 48
211:
	jmp 29f
28:
	mov ebx, 51
	mov eax, 32
29:
	jmp 27f
26:
	mov ebx, 47
	mov eax, 28
27:
	jmp 25f
24:
	mov ebx, 35
	mov eax, 20
25:
	jmp 23f
22:
	mov ebx, 34
	mov eax, 16
23:
	cmp ebp, eax
	jne 226f
	mov eax, ebx
	add eax, 11
	cmp ecx, eax
	jb 228f
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, ecx
	sub eax, ebx
	sub eax, 3
	mov ebx, eax
	mov eax, 255
230:
	mov BYTE PTR [edi], al
	add edi, 1
	sub ebx, 1
	jne 230b
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
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
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 81
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 10
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 64
	mov BYTE PTR [edi], al
	add edi, 1
254:
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 65
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 8
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 7
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 81
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 64
	mov BYTE PTR [edi], al
	add edi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 65
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 33
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 43
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 14
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 26
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 20
	mov BYTE PTR [edi], al
	add edi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 12
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 8
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 42
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 247
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 16
	mov BYTE PTR [edi], al
	add edi, 1
232:
255:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ebp, 1
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
	mov esi, esp
	add esi, 64
	mov edi, esp
	add edi, 1088
	mov ecx, DWORD PTR [esp+2136]
	mov ebp, 0
258:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 258b
	mov eax, 0
	sub eax, ebp
	or eax, ebp
	shr eax, 31
	xor eax, 1
	mov ecx, DWORD PTR [esp+40]
	and eax, ecx
	jmp 257f
256:
	mov eax, 0
257:
	jmp 21f
20:
	mov eax, 0
21:
	lea esp, [esp+2112]
	mov edi, DWORD PTR [esp]
	mov ebp, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+4]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2228]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	mov DWORD PTR [esp+2224], ecx
	lea esp, [esp+2228]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_rsa_pkcs1_recover_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-2112]
	mov eax, DWORD PTR [esp+2164]
	cmp eax, DWORD PTR [esp+2144]
	jne 20f
	mov eax, esp
	add eax, 64
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+2144]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2148]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2152]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2160]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2144]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2168]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2172]
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov DWORD PTR [esp+40], eax
	mov edi, esp
	add edi, 1088
	mov ecx, DWORD PTR [esp+2144]
	mov edx, DWORD PTR [esp+2156]
	mov ebp, DWORD PTR [esp+2136]
	mov esi, esp
	add esi, 64
	add esi, DWORD PTR [esp+2144]
	sub esi, DWORD PTR [esp+2136]
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
	mov ebx, 2048
	mov eax, 0
	jmp 225f
224:
	mov ebx, 83
	mov eax, 64
225:
	jmp 223f
222:
	mov ebx, 67
	mov eax, 48
223:
	jmp 221f
220:
	mov ebx, 51
	mov eax, 32
221:
	jmp 219f
218:
	mov ebx, 47
	mov eax, 28
219:
	jmp 217f
216:
	mov ebx, 51
	mov eax, 32
217:
	jmp 215f
214:
	mov ebx, 47
	mov eax, 28
215:
	jmp 213f
212:
	mov ebx, 83
	mov eax, 64
213:
	jmp 211f
210:
	mov ebx, 67
	mov eax, 48
211:
	jmp 29f
28:
	mov ebx, 51
	mov eax, 32
29:
	jmp 27f
26:
	mov ebx, 47
	mov eax, 28
27:
	jmp 25f
24:
	mov ebx, 35
	mov eax, 20
25:
	jmp 23f
22:
	mov ebx, 34
	mov eax, 16
23:
	cmp ebp, eax
	jne 226f
	mov eax, ebx
	add eax, 11
	cmp ecx, eax
	jb 228f
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, ecx
	sub eax, ebx
	sub eax, 3
	mov ebx, eax
	mov eax, 255
230:
	mov BYTE PTR [edi], al
	add edi, 1
	sub ebx, 1
	jne 230b
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
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
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 81
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 10
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 64
	mov BYTE PTR [edi], al
	add edi, 1
254:
	jmp 252f
251:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 65
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 8
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 7
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 81
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 64
	mov BYTE PTR [edi], al
	add edi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 65
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 33
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 43
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 14
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 26
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 20
	mov BYTE PTR [edi], al
	add edi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 12
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 8
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 42
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 247
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 16
	mov BYTE PTR [edi], al
	add edi, 1
232:
255:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ebp, 1
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
	mov esi, esp
	add esi, 64
	mov edi, esp
	add edi, 1088
	mov ecx, DWORD PTR [esp+2144]
	mov ebp, 0
258:
	movzx eax, BYTE PTR [esi]
	movzx edx, BYTE PTR [edi]
	xor eax, edx
	or ebp, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 258b
	mov eax, 0
	sub eax, ebp
	or eax, ebp
	shr eax, 31
	xor eax, 1
	mov ecx, DWORD PTR [esp+40]
	and eax, ecx
	mov ebx, eax
	mov edx, 0
	sub edx, eax
	mov edi, DWORD PTR [esp+2132]
	mov ecx, DWORD PTR [esp+2136]
	mov esi, esp
	add esi, 64
	add esi, DWORD PTR [esp+2144]
	sub esi, DWORD PTR [esp+2136]
259:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	mov eax, 0
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 259b
	mov eax, ebx
	jmp 257f
256:
	mov esi, DWORD PTR [esp+2132]
	mov ecx, DWORD PTR [esp+2136]
	mov eax, 0
260:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 260b
257:
	jmp 21f
20:
	mov esi, DWORD PTR [esp+2132]
	mov ecx, DWORD PTR [esp+2136]
	mov eax, 0
261:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 261b
21:
	lea esp, [esp+2112]
	mov edi, DWORD PTR [esp]
	mov ebp, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+4]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2228]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	mov DWORD PTR [esp+2224], ecx
	lea esp, [esp+2228]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_rsa_pkcs1_sign_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-1120]
	mov edi, esp
	add edi, 96
	mov ecx, DWORD PTR [esp+1152]
	mov edx, DWORD PTR [esp+1164]
	mov esi, DWORD PTR [esp+1168]
	mov ebp, DWORD PTR [esp+1172]
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
	mov ebx, 2048
	mov eax, 0
	jmp 223f
222:
	mov ebx, 83
	mov eax, 64
223:
	jmp 221f
220:
	mov ebx, 67
	mov eax, 48
221:
	jmp 219f
218:
	mov ebx, 51
	mov eax, 32
219:
	jmp 217f
216:
	mov ebx, 47
	mov eax, 28
217:
	jmp 215f
214:
	mov ebx, 51
	mov eax, 32
215:
	jmp 213f
212:
	mov ebx, 47
	mov eax, 28
213:
	jmp 211f
210:
	mov ebx, 83
	mov eax, 64
211:
	jmp 29f
28:
	mov ebx, 67
	mov eax, 48
29:
	jmp 27f
26:
	mov ebx, 51
	mov eax, 32
27:
	jmp 25f
24:
	mov ebx, 47
	mov eax, 28
25:
	jmp 23f
22:
	mov ebx, 35
	mov eax, 20
23:
	jmp 21f
20:
	mov ebx, 34
	mov eax, 16
21:
	cmp ebp, eax
	jne 224f
	mov eax, ebx
	add eax, 11
	cmp ecx, eax
	jb 226f
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, ecx
	sub eax, ebx
	sub eax, 3
	mov ebx, eax
	mov eax, 255
228:
	mov BYTE PTR [edi], al
	add edi, 1
	sub ebx, 1
	jne 228b
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
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
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 81
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 10
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 64
	mov BYTE PTR [edi], al
	add edi, 1
252:
	jmp 250f
249:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 65
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
250:
	jmp 248f
247:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 8
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
248:
	jmp 246f
245:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 7
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
246:
	jmp 244f
243:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
244:
	jmp 242f
241:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
242:
	jmp 240f
239:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 81
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 64
	mov BYTE PTR [edi], al
	add edi, 1
240:
	jmp 238f
237:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 65
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
238:
	jmp 236f
235:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 49
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
236:
	jmp 234f
233:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 45
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 96
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 1
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 101
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 28
	mov BYTE PTR [edi], al
	add edi, 1
234:
	jmp 232f
231:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 33
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 9
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 43
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 14
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 3
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 26
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 20
	mov BYTE PTR [edi], al
	add edi, 1
232:
	jmp 230f
229:
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 32
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 48
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 12
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 6
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 8
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 42
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 72
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 134
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 247
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 13
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 2
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 5
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 4
	mov BYTE PTR [edi], al
	add edi, 1
	mov eax, 16
	mov BYTE PTR [edi], al
	add edi, 1
230:
253:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ebp, 1
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
	mov eax, DWORD PTR [esp+1140]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+1144]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1148]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1152]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1156]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1160]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 96
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1152]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+1176]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+1180]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+1184]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+1188]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+1192]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+1196]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+1200]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+1204]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+1208]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+1212]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+1216]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+1220]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+1224]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+1228]
	mov DWORD PTR [esp+84], eax
	call {vg_rsa_private_checked_precomputed}
	mov ebx, eax
	mov eax, 0
	mov esi, esp
	add esi, 96
	mov ecx, DWORD PTR [esp+1152]
256:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 256b
	mov eax, ebx
	jmp 255f
254:
	mov esi, DWORD PTR [esp+1140]
	mov ecx, DWORD PTR [esp+1144]
	mov eax, 0
257:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 257b
255:
	lea esp, [esp+1120]
	mov edi, DWORD PTR [esp]
	mov ebp, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+4]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-4080]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	movdqu XMMWORD PTR [esp+2880], xmm0
	movdqu XMMWORD PTR [esp+2896], xmm0
	movdqu XMMWORD PTR [esp+2912], xmm0
	movdqu XMMWORD PTR [esp+2928], xmm0
	movdqu XMMWORD PTR [esp+2944], xmm0
	movdqu XMMWORD PTR [esp+2960], xmm0
	movdqu XMMWORD PTR [esp+2976], xmm0
	movdqu XMMWORD PTR [esp+2992], xmm0
	movdqu XMMWORD PTR [esp+3008], xmm0
	movdqu XMMWORD PTR [esp+3024], xmm0
	movdqu XMMWORD PTR [esp+3040], xmm0
	movdqu XMMWORD PTR [esp+3056], xmm0
	movdqu XMMWORD PTR [esp+3072], xmm0
	movdqu XMMWORD PTR [esp+3088], xmm0
	movdqu XMMWORD PTR [esp+3104], xmm0
	movdqu XMMWORD PTR [esp+3120], xmm0
	movdqu XMMWORD PTR [esp+3136], xmm0
	movdqu XMMWORD PTR [esp+3152], xmm0
	movdqu XMMWORD PTR [esp+3168], xmm0
	movdqu XMMWORD PTR [esp+3184], xmm0
	movdqu XMMWORD PTR [esp+3200], xmm0
	movdqu XMMWORD PTR [esp+3216], xmm0
	movdqu XMMWORD PTR [esp+3232], xmm0
	movdqu XMMWORD PTR [esp+3248], xmm0
	movdqu XMMWORD PTR [esp+3264], xmm0
	movdqu XMMWORD PTR [esp+3280], xmm0
	movdqu XMMWORD PTR [esp+3296], xmm0
	movdqu XMMWORD PTR [esp+3312], xmm0
	movdqu XMMWORD PTR [esp+3328], xmm0
	movdqu XMMWORD PTR [esp+3344], xmm0
	movdqu XMMWORD PTR [esp+3360], xmm0
	movdqu XMMWORD PTR [esp+3376], xmm0
	movdqu XMMWORD PTR [esp+3392], xmm0
	movdqu XMMWORD PTR [esp+3408], xmm0
	movdqu XMMWORD PTR [esp+3424], xmm0
	movdqu XMMWORD PTR [esp+3440], xmm0
	movdqu XMMWORD PTR [esp+3456], xmm0
	movdqu XMMWORD PTR [esp+3472], xmm0
	movdqu XMMWORD PTR [esp+3488], xmm0
	movdqu XMMWORD PTR [esp+3504], xmm0
	movdqu XMMWORD PTR [esp+3520], xmm0
	movdqu XMMWORD PTR [esp+3536], xmm0
	movdqu XMMWORD PTR [esp+3552], xmm0
	movdqu XMMWORD PTR [esp+3568], xmm0
	movdqu XMMWORD PTR [esp+3584], xmm0
	movdqu XMMWORD PTR [esp+3600], xmm0
	movdqu XMMWORD PTR [esp+3616], xmm0
	movdqu XMMWORD PTR [esp+3632], xmm0
	movdqu XMMWORD PTR [esp+3648], xmm0
	movdqu XMMWORD PTR [esp+3664], xmm0
	movdqu XMMWORD PTR [esp+3680], xmm0
	movdqu XMMWORD PTR [esp+3696], xmm0
	movdqu XMMWORD PTR [esp+3712], xmm0
	movdqu XMMWORD PTR [esp+3728], xmm0
	movdqu XMMWORD PTR [esp+3744], xmm0
	movdqu XMMWORD PTR [esp+3760], xmm0
	movdqu XMMWORD PTR [esp+3776], xmm0
	movdqu XMMWORD PTR [esp+3792], xmm0
	movdqu XMMWORD PTR [esp+3808], xmm0
	movdqu XMMWORD PTR [esp+3824], xmm0
	movdqu XMMWORD PTR [esp+3840], xmm0
	movdqu XMMWORD PTR [esp+3856], xmm0
	movdqu XMMWORD PTR [esp+3872], xmm0
	movdqu XMMWORD PTR [esp+3888], xmm0
	movdqu XMMWORD PTR [esp+3904], xmm0
	movdqu XMMWORD PTR [esp+3920], xmm0
	movdqu XMMWORD PTR [esp+3936], xmm0
	movdqu XMMWORD PTR [esp+3952], xmm0
	movdqu XMMWORD PTR [esp+3968], xmm0
	movdqu XMMWORD PTR [esp+3984], xmm0
	movdqu XMMWORD PTR [esp+4000], xmm0
	movdqu XMMWORD PTR [esp+4016], xmm0
	movdqu XMMWORD PTR [esp+4032], xmm0
	movdqu XMMWORD PTR [esp+4048], xmm0
	movdqu XMMWORD PTR [esp+4064], xmm0
	lea esp, [esp-504]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	lea esp, [esp+504]
	lea esp, [esp+4080]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
