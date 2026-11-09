// The functions of `src/internal/vg_dsa_derive_key_checked_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_derive_key_checked_adx:
	mov r11, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rbx
	mov QWORD PTR [r11+8], rbp
	mov QWORD PTR [r11+16], r12
	mov QWORD PTR [r11+24], r13
	mov QWORD PTR [r11+32], r14
	mov QWORD PTR [r11+40], r15
	mov eax, 0
	mov QWORD PTR [r11+296], rax
	mov QWORD PTR [r11+304], rax
	mov QWORD PTR [r11+312], rax
	mov QWORD PTR [r11+344], rax
	mov QWORD PTR [r11+320], rdi
	mov QWORD PTR [r11+256], rdx
	mov QWORD PTR [r11+328], r8
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r11+336], rax
	mov rax, QWORD PTR [r11+256]
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+264], rax
	add rax, QWORD PTR [r11+336]
	mov QWORD PTR [r11+272], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+280], rax
	add rax, QWORD PTR [r11+328]
	mov QWORD PTR [r11+288], rax
	mov rdi, r11
	mov QWORD PTR [r11+288], r9
	mov rax, r11
	add rax, 15712
	mov QWORD PTR [r11+280], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	mov r8d, 0
	mov r9d, 0
20:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 21f
	jmp 22f
21:
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov r8, rcx
	mov r9, rax
24:
22:
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov QWORD PTR [rdi+176], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
	mov r9d, 0
25:
	movzx eax, BYTE PTR [rsi]
	test r8, r8
	je 26f
	jmp 27f
26:
	test rax, rax
	jne 28f
	jmp 29f
28:
	mov r8, rcx
	mov r9, rax
29:
27:
	add rsi, 1
	sub rcx, 1
	jne 25b
	mov QWORD PTR [rdi+352], r8
	cmp r9, 128
	sbb rax, rax
	xor rax, -1
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rdx, QWORD PTR [rdi+176]
	cmp rdx, 128
	je 210f
	cmp rdx, 256
	je 212f
	cmp rdx, 384
	je 214f
	mov eax, 0
	jmp 215f
214:
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
215:
	jmp 213f
212:
	mov rax, r8
	xor rax, 28
	cmp rax, 1
	sbb rax, rax
	mov r10, rax
	mov rax, r8
	xor rax, 32
	cmp rax, 1
	sbb rax, rax
	or rax, r10
	mov r10, rax
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
	or rax, r10
213:
	jmp 211f
210:
	mov rax, r8
	xor rax, 20
	cmp rax, 1
	sbb rax, rax
211:
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, QWORD PTR [rdi+328]
	movzx eax, BYTE PTR [rsi+rcx*1-1]
	mov rsi, QWORD PTR [rdi+264]
	mov rcx, QWORD PTR [rdi+336]
	movzx edx, BYTE PTR [rsi+rcx*1-1]
	and rax, rdx
	and rax, 1
	mov edx, 0
	sub rdx, rax
	mov rax, rdx
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+344]
	mov rdx, QWORD PTR [rdi+352]
	cmp rdx, rax
	cmovb rax, rdx
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rdi+360]
	test rax, rax
	je 216f
	mov r12d, 48
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 3456
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
218:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 218b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
219:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 220f
	jmp 221f
220:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
221:
	test rdx, rdx
	jne 219b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	mov rsi, rdi
	mov r12, QWORD PTR [rdi+136]
	add r12, 7
	shr r12, 3
	add rdi, 13312
	mov QWORD PTR [rdi+48], r12
	mov QWORD PTR [rdi+128], rsi
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
222:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
223:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 224f
	jmp 225f
224:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
225:
	test rdx, rdx
	jne 223b
	mov rbx, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rbx]
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov QWORD PTR [rdi+56], r15
	mov rdi, QWORD PTR [rdi+128]
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+136], rax
	add rdi, 13312
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
229:
	test rdx, rdx
	jne 227b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
230:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 230b
	mov r15, QWORD PTR [rbx]
	mov r14, 1
231:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 231b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+152], rax
	mov rax, rdi
	add rax, 15328
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 233f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 235f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 237f
239:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 239b
	jmp 238f
237:
238:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
240:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 240b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
241:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
242:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 242b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
243:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 243b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
244:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 244b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 241b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
245:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 245b
	jmp 236f
235:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
246:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 246b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
247:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 247b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
248:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
249:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 249b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
250:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
251:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 251b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
252:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 252b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 248b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
253:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 253b
236:
	jmp 234f
233:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
254:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 254b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
255:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
256:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 256b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
257:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 257b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
258:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 258b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 255b
234:
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
259:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 259b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
260:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 261f
	jmp 262f
261:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
262:
	test rdx, rdx
	jne 260b
	mov edx, 6
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov edx, 5
	mov ecx, 1
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+96]
	mov r14, 0
263:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 263b
	mov rax, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rax+144]
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rax+152]
	mov QWORD PTR [rdi+144], rdx
	mov edx, 0
	mov QWORD PTR [rdi+152], rdx
	mov rax, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
264:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 264b
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
265:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 265b
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+96]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
266:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 266b
	mov eax, 14
	mov QWORD PTR [rdi+160], rax
267:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	mov rdx, QWORD PTR [rdi+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov QWORD PTR [rdi+208], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+208]
	mov r14, 0
268:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 268b
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 267b
269:
	mov rax, QWORD PTR [rdi+136]
	mov rcx, QWORD PTR [rdi+152]
	movzx eax, BYTE PTR [rax+rcx*1]
	mov QWORD PTR [rdi+168], rax
	mov eax, 2
	mov QWORD PTR [rdi+160], rax
270:
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov edx, 6
	mov ecx, 6
	mov r8d, 6
	call {vg_rsa_lazy_mont_mul_adx}
	mov rdx, QWORD PTR [rdi+168]
	mov rax, rdx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rdi+168], rax
	shr rdx, 4
	and rdx, 15
	mov QWORD PTR [rdi+216], rdx
	mov rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
271:
	mov r15, QWORD PTR [rdi+224]
	mov rcx, QWORD PTR [rdi+208]
	mov r12, QWORD PTR [rdi+48]
	mov r11, r12
	add r11, 2
	add r11, r11
	add r11, r11
	add r11, r11
	mov r13, r12
	add r13, 1
	shr r13, 1
	add r13, r13
	mov rbx, QWORD PTR [rdi+104]
	mov r14, r15
	add r14, 0
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm8, r14
	punpcklqdq xmm8, xmm8
	mov r14, r15
	add r14, 1
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm9, r14
	punpcklqdq xmm9, xmm9
	mov r14, r15
	add r14, 2
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm10, r14
	punpcklqdq xmm10, xmm10
	mov r14, r15
	add r14, 3
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm11, r14
	punpcklqdq xmm11, xmm11
	mov r14, r15
	add r14, 4
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm12, r14
	punpcklqdq xmm12, xmm12
	mov r14, r15
	add r14, 5
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm13, r14
	punpcklqdq xmm13, xmm13
	mov r14, r15
	add r14, 6
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm14, r14
	punpcklqdq xmm14, xmm14
	mov r14, r15
	add r14, 7
	xor r14, QWORD PTR [rdi+216]
	cmp r14, 1
	sbb r14, r14
	movq xmm15, r14
	punpcklqdq xmm15, xmm15
	mov r14, r15
	add r14, 0
	xor r14, 8
	cmp r14, 1
	sbb r14, r14
	movq xmm7, r14
	punpcklqdq xmm7, xmm7
	mov rdx, rcx
	add rdx, r11
	mov rsi, rdx
	add rsi, r11
	mov rbp, rsi
	add rbp, r11
	mov r8, rbp
	add r8, r11
	mov r9, r8
	add r9, r11
	mov r10, r9
	add r10, r11
	mov rax, r10
	add rax, r11
	mov r14d, 0
272:
	movdqu xmm0, XMMWORD PTR [rcx+r14*8]
	pand xmm0, xmm8
	movdqu xmm1, XMMWORD PTR [rdx+r14*8]
	pand xmm1, xmm9
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rsi+r14*8]
	pand xmm1, xmm10
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbp+r14*8]
	pand xmm1, xmm11
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r8+r14*8]
	pand xmm1, xmm12
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r9+r14*8]
	pand xmm1, xmm13
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [r10+r14*8]
	pand xmm1, xmm14
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rax+r14*8]
	pand xmm1, xmm15
	por xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [rbx+r14*8]
	pand xmm1, xmm7
	por xmm0, xmm1
	movdqu XMMWORD PTR [rbx+r14*8], xmm0
	add r14, 2
	cmp r14, r13
	jne 272b
	add rax, r11
	mov QWORD PTR [rdi+208], rax
	mov rax, r15
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, 16
	jne 271b
	mov edx, 6
	mov ecx, 6
	mov r8d, 5
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+160]
	sub rax, 1
	mov QWORD PTR [rdi+160], rax
	jne 270b
	mov rax, QWORD PTR [rdi+152]
	add rax, 1
	mov QWORD PTR [rdi+152], rax
	cmp rax, QWORD PTR [rdi+144]
	jne 269b
	mov edx, 6
	mov ecx, 6
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
273:
	mov rbp, rdx
	and rbp, 7
	je 274f
	jmp 275f
274:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
275:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 273b
	mov rdi, QWORD PTR [rdi+128]
	mov rsi, rdi
	add rsi, 15328
	mov rdx, rdi
	add rdx, 15712
	mov rcx, QWORD PTR [rdi+328]
	mov r8, -1
276:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 276b
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
277:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 277b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
278:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 279f
	jmp 280f
279:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
280:
	test rdx, rdx
	jne 278b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
281:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 281b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
282:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 282b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	add rdi, 3456
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
283:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 283b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov rbx, QWORD PTR [rdi+72]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
284:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 285f
	jmp 286f
285:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
286:
	test rdx, rdx
	jne 284b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
287:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 287b
	mov r15, QWORD PTR [rbx]
	shr r15, 1
	mov r14, 1
288:
	mov rax, QWORD PTR [rbx+r14*8]
	or r15, rax
	add r14, 1
	cmp r14, r12
	jne 288b
	cmp r15, 1
	sbb rax, rax
	xor rax, -1
	and rax, rbp
	mov rdi, QWORD PTR [rdi+128]
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+168], rax
	add rdi, 3456
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 1
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
289:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 289b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
290:
	mov rbp, rdx
	and rbp, 7
	je 291f
	jmp 292f
291:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
292:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 290b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14944
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+136], rax
	mov rax, rdi
	add rax, 14816
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+120]
	mov eax, 0
	mov r14, 0
293:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 293b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov r12, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rdi+64]
	mov rax, QWORD PTR [r10+r12*8-8]
	test rax, rax
	je 294f
	mov rax, QWORD PTR [r10+r12*8-8]
	shr rax, 63
	xor rax, 1
	mov rcx, r12
	and rcx, 3
	or rax, rcx
	je 296f
	mov rax, QWORD PTR [r10+r12*8-8]
	mov edx, 1
	mov ecx, 64
	cmp rax, 1
	je 298f
2100:
	shr rax, 1
	add rdx, rdx
	sub rcx, 1
	cmp rax, 1
	jne 2100b
	jmp 299f
298:
299:
	mov QWORD PTR [rdi+208], rcx
	mov rcx, r12
	sub rcx, 1
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2101:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2101b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+208]
	add rcx, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+208], rcx
2102:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2103:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2103b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2104:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2104b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2105:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2105b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2102b
	mov eax, 6
	mov QWORD PTR [rdi+208], rax
2106:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2106b
	jmp 297f
296:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2107:
	mov eax, 0
	add rbp, rbp
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2107b
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, rsi
	xor rdx, -1
	mov rax, -1
	mov ecx, 0
	mov r13d, 64
2108:
	add rax, rax
	adc rdx, rdx
	sbb r11, r11
	mov r14, rdx
	sub r14, rsi
	sbb r15, r15
	xor r15, -1
	or r15, r11
	test r15, r15
	cmovne rdx, r14
	add rcx, rcx
	sub rcx, r15
	sub r13, 1
	jne 2108b
	mov QWORD PTR [r8], rcx
	mov rcx, QWORD PTR [rdi+48]
	shr rcx, 2
	mov QWORD PTR [rdi+208], rcx
2109:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rbp, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [r10+r12*8-8]
	mov rdx, QWORD PTR [rbx+r12*8-8]
	mov rax, QWORD PTR [rbx+r12*8-16]
	mov r9, rsi
	sub r9, rdx
	cmp r9, 1
	sbb r9, r9
	mov r11, r9
	xor r11, -1
	and rdx, r11
	mov r14, rax
	mov r13, rdx
	mov rax, QWORD PTR [rbp]
	mul r13
	add rax, r14
	adc rdx, r13
	mov rcx, rdx
	add rcx, 1
	mov r13, rax
	mov rax, rcx
	mul rsi
	sub r14, rax
	cmp r13, r14
	sbb r15, r15
	add rcx, r15
	and r15, rsi
	add r14, r15
	mov r15, rsi
	sub r15, 1
	cmp r15, r14
	adc rcx, 0
	or rcx, r9
	mov rax, QWORD PTR [r10]
	mul rcx
	mov r9, rdx
	mov edx, 0
	sub rdx, rax
	mov QWORD PTR [r8], rdx
	sbb rbp, rbp
	mov r14, 1
2110:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, r9
	adc rdx, 0
	mov r9, rdx
	mov rdx, QWORD PTR [rbx+r14*8-8]
	add rbp, rbp
	sbb rdx, rax
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rdx
	add r14, 1
	cmp r14, r12
	jne 2110b
	mov rdx, QWORD PTR [rbx+r12*8-8]
	add rbp, rbp
	sbb rdx, r9
	mov QWORD PTR [r8+r12*8], rdx
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2111:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2111b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rax
	sbb r11, r11
	mov ebp, 0
	mov r14, 0
2112:
	mov rax, QWORD PTR [r10+r14*8]
	and rax, r11
	add rbp, rbp
	adc rax, QWORD PTR [r8+r14*8]
	sbb rbp, rbp
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2112b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rsi, r8
	mov r14, 0
2113:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2113b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2109b
	mov eax, 2
	mov QWORD PTR [rdi+208], rax
2114:
	mov edx, 4
	mov ecx, 4
	mov r8d, 4
	call {vg_rsa_mont_mul_adx}
	mov rax, QWORD PTR [rdi+208]
	sub rax, 1
	mov QWORD PTR [rdi+208], rax
	jne 2114b
297:
	jmp 295f
294:
	mov r12, QWORD PTR [rdi+48]
	mov edx, 1
	mov ecx, 0
	mov r8, QWORD PTR [rdi+96]
	mov eax, 0
	mov r14, 0
2115:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2115b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov QWORD PTR [r8+rcx*8], rdx
	mov rcx, QWORD PTR [rdi+48]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	mov QWORD PTR [rdi+208], rcx
2116:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2117:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2117b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2118:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2118b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2119:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2119b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2116b
295:
	mov edx, 4
	mov ecx, 4
	mov r8d, 7
	call {vg_rsa_mont_mul_adx}
	mov ecx, 8
	mov QWORD PTR [rdi+208], rcx
2120:
	mov rbx, QWORD PTR [rdi+96]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2121:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2121b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
2122:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2122b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2123:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2123b
	mov rcx, QWORD PTR [rdi+208]
	sub rcx, 1
	mov QWORD PTR [rdi+208], rcx
	jne 2120b
	mov r8, QWORD PTR [rdi+112]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2124:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2124b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r8, QWORD PTR [rdi+72]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
2125:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2125b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+128]
	mov rcx, QWORD PTR [rax+136]
	mov QWORD PTR [rdi+184], rsi
	mov QWORD PTR [rdi+176], rcx
	test rcx, rcx
	je 2126f
2128:
	mov rsi, QWORD PTR [rdi+184]
	movzx eax, BYTE PTR [rsi]
	mov rbx, QWORD PTR [rdi+72]
	mov QWORD PTR [rbx], rax
	add rsi, 1
	mov QWORD PTR [rdi+184], rsi
	mov edx, 6
	mov ecx, 4
	mov r8d, 6
	call {vg_rsa_mont_mul_adx}
	mov rbx, QWORD PTR [rdi+112]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
2129:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, QWORD PTR [r9+r14*8]
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2129b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov rbx, QWORD PTR [rdi+112]
	mov ebp, 0
	mov r14, 0
2130:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2130b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
2131:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 2131b
	mov rax, QWORD PTR [rdi+176]
	sub rax, 1
	mov QWORD PTR [rdi+176], rax
	jne 2128b
	jmp 2127f
2126:
2127:
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2132:
	mov rbp, rdx
	and rbp, 7
	je 2133f
	jmp 2134f
2133:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2134:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2132b
	mov rdi, QWORD PTR [rdi+128]
	mov rax, rdi
	add rax, 14816
	mov rsi, rax
	mov rcx, QWORD PTR [rdi+336]
	mov r8d, 0
2135:
	movzx eax, BYTE PTR [rsi]
	or r8, rax
	add rsi, 1
	sub rcx, 1
	jne 2135b
	cmp r8, 1
	sbb rax, rax
	and rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, rdi
	add rax, 14912
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+168], rax
	add rdi, 13312
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+64]
	mov rbx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rsi]
	sub rax, 2
	mov QWORD PTR [rbx], rax
	sbb rbp, rbp
	mov r14, 1
2136:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	sbb rax, 0
	mov QWORD PTR [rbx+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 2136b
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+160]
	mov rcx, QWORD PTR [rax+168]
	mov rbx, QWORD PTR [rdi+112]
	mov r15, -1
	mov edx, 0
	mov r14, rsi
	add r14, rcx
2137:
	mov rbp, rdx
	and rbp, 7
	je 2138f
	jmp 2139f
2138:
	mov rbp, rdx
	shr rbp, 3
	mov rax, QWORD PTR [rbx+rbp*8]
	and rax, r15
2139:
	sub r14, 1
	mov BYTE PTR [r14], al
	shr rax, 8
	add rdx, 1
	cmp rdx, rcx
	jne 2137b
	mov rdi, QWORD PTR [rdi+128]
	mov r8, QWORD PTR [rdi+360]
	mov r13, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+280]
	mov r10, QWORD PTR [rdi+288]
	mov r11, QWORD PTR [rdi+328]
	mov r12, QWORD PTR [rdi+336]
	mov rdx, r13
	mov rsi, QWORD PTR [rdi+256]
	mov rcx, r11
	add rcx, rcx
	add rcx, r12
2140:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2140b
	mov rdx, r13
	add rdx, r11
	add rdx, r11
	add rdx, r12
	mov rsi, r9
	mov rcx, r11
2141:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2141b
	mov rdx, r13
	add rdx, r11
	add rdx, r11
	add rdx, r11
	add rdx, r12
	mov rsi, r10
	mov rcx, r12
2142:
	movzx eax, BYTE PTR [rsi]
	and rax, r8
	mov BYTE PTR [rdx], al
	add rsi, 1
	add rdx, 1
	sub rcx, 1
	jne 2142b
	mov rax, QWORD PTR [rdi+360]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	jmp 217f
216:
	mov rsi, QWORD PTR [rdi+320]
	mov rcx, QWORD PTR [rdi+328]
	add rcx, rcx
	add rcx, QWORD PTR [rdi+328]
	add rcx, QWORD PTR [rdi+336]
	add rcx, QWORD PTR [rdi+336]
	mov eax, 0
2143:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 2143b
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
217:
	ret
	.p2align 6
