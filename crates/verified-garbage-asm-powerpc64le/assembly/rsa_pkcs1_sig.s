// The functions of `src/rsa_pkcs1_sig.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_verify_precomputed:
	addi %r12, %r1, 0
	ld %r11, 96(%r12)
	subf %r11, %r4, %r11
	cmpldi %cr0, %r11, 0
	bne %cr0, 20f
	stdu %r1, -2224(%r1)
	addi %r12, %r1, 0
	std %r28, 112(%r12)
	std %r29, 120(%r12)
	std %r30, 128(%r12)
	std %r31, 136(%r12)
	mflr %r0
	std %r0, 144(%r12)
	or %r28, %r4, %r4
	rlwinm %r29, %r7, 0, 0, 31
	or %r30, %r8, %r8
	or %r31, %r9, %r9
	or %r9, %r10, %r10
	or %r10, %r4, %r4
	or %r7, %r5, %r5
	or %r8, %r6, %r6
	ld %r0, 2328(%r12)
	std %r0, 96(%r12)
	ld %r0, 2336(%r12)
	std %r0, 104(%r12)
	ld %r5, 2344(%r12)
	ld %r6, 2352(%r12)
	addi %r3, %r12, 168
	bl {vg_rsa_public_precomputed_checked}
	addi %r12, %r1, 0
	std %r3, 152(%r12)
	addi %r4, %r12, 1192
	or %r5, %r28, %r28
	or %r6, %r29, %r29
	or %r7, %r30, %r30
	or %r8, %r31, %r31
	addi %r9, %r6, -0
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	addi %r9, %r6, -1
	cmplwi %cr0, %r9, 0
	beq %cr0, 24f
	addi %r9, %r6, -2
	cmplwi %cr0, %r9, 0
	beq %cr0, 26f
	addi %r9, %r6, -3
	cmplwi %cr0, %r9, 0
	beq %cr0, 28f
	addi %r9, %r6, -4
	cmplwi %cr0, %r9, 0
	beq %cr0, 210f
	addi %r9, %r6, -5
	cmplwi %cr0, %r9, 0
	beq %cr0, 212f
	addi %r9, %r6, -6
	cmplwi %cr0, %r9, 0
	beq %cr0, 214f
	addi %r9, %r6, -7
	cmplwi %cr0, %r9, 0
	beq %cr0, 216f
	addi %r9, %r6, -8
	cmplwi %cr0, %r9, 0
	beq %cr0, 218f
	addi %r9, %r6, -9
	cmplwi %cr0, %r9, 0
	beq %cr0, 220f
	addi %r9, %r6, -10
	cmplwi %cr0, %r9, 0
	beq %cr0, 222f
	addi %r9, %r6, -11
	cmplwi %cr0, %r9, 0
	beq %cr0, 224f
	li %r9, 2048
	li %r10, 0
	b 225f
224:
	li %r9, 83
	li %r10, 64
225:
	b 223f
222:
	li %r9, 67
	li %r10, 48
223:
	b 221f
220:
	li %r9, 51
	li %r10, 32
221:
	b 219f
218:
	li %r9, 47
	li %r10, 28
219:
	b 217f
216:
	li %r9, 51
	li %r10, 32
217:
	b 215f
214:
	li %r9, 47
	li %r10, 28
215:
	b 213f
212:
	li %r9, 83
	li %r10, 64
213:
	b 211f
210:
	li %r9, 67
	li %r10, 48
211:
	b 29f
28:
	li %r9, 51
	li %r10, 32
29:
	b 27f
26:
	li %r9, 47
	li %r10, 28
27:
	b 25f
24:
	li %r9, 35
	li %r10, 20
25:
	b 23f
22:
	li %r9, 34
	li %r10, 16
23:
	subf %r11, %r10, %r8
	cmpldi %cr0, %r11, 0
	bne %cr0, 226f
	addi %r11, %r9, 11
	subf %r11, %r11, %r5
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	bne %cr0, 228f
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	subf %r11, %r9, %r5
	addi %r11, %r11, -3
	li %r0, 255
230:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 230b
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r9, %r6, -0
	cmplwi %cr0, %r9, 0
	beq %cr0, 231f
	addi %r9, %r6, -1
	cmplwi %cr0, %r9, 0
	beq %cr0, 233f
	addi %r9, %r6, -2
	cmplwi %cr0, %r9, 0
	beq %cr0, 235f
	addi %r9, %r6, -3
	cmplwi %cr0, %r9, 0
	beq %cr0, 237f
	addi %r9, %r6, -4
	cmplwi %cr0, %r9, 0
	beq %cr0, 239f
	addi %r9, %r6, -5
	cmplwi %cr0, %r9, 0
	beq %cr0, 241f
	addi %r9, %r6, -6
	cmplwi %cr0, %r9, 0
	beq %cr0, 243f
	addi %r9, %r6, -7
	cmplwi %cr0, %r9, 0
	beq %cr0, 245f
	addi %r9, %r6, -8
	cmplwi %cr0, %r9, 0
	beq %cr0, 247f
	addi %r9, %r6, -9
	cmplwi %cr0, %r9, 0
	beq %cr0, 249f
	addi %r9, %r6, -10
	cmplwi %cr0, %r9, 0
	beq %cr0, 251f
	addi %r9, %r6, -11
	cmplwi %cr0, %r9, 0
	beq %cr0, 253f
	b 254f
253:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 81
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 10
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 64
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
254:
	b 252f
251:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 65
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
252:
	b 250f
249:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 8
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
250:
	b 248f
247:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 7
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
248:
	b 246f
245:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
246:
	b 244f
243:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
244:
	b 242f
241:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 81
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 64
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
242:
	b 240f
239:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 65
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
240:
	b 238f
237:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
238:
	b 236f
235:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
236:
	b 234f
233:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 33
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 43
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 14
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 26
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 20
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
234:
	b 232f
231:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 12
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 8
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 42
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 247
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 16
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
232:
255:
	lbz %r0, 0(%r7)
	stb %r0, 0(%r4)
	addi %r7, %r7, 1
	addi %r4, %r4, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 255b
	li %r3, 1
	b 229f
228:
	li %r3, 0
229:
	b 227f
226:
	li %r3, 0
227:
	cmpldi %cr0, %r3, 0
	beq %cr0, 256f
	addi %r12, %r1, 0
	addi %r4, %r12, 168
	addi %r5, %r12, 1192
	or %r6, %r28, %r28
	li %r7, 0
258:
	lbz %r8, 0(%r4)
	lbz %r9, 0(%r5)
	xor %r8, %r8, %r9
	or %r7, %r7, %r8
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 258b
	addi %r3, %r7, -1
	rldicl %r3, %r3, 1, 63
	b 257f
256:
	li %r3, 0
257:
	addi %r12, %r1, 0
	ld %r4, 152(%r12)
	and %r3, %r3, %r4
	addi %r12, %r1, 0
	ld %r0, 144(%r12)
	mtlr %r0
	ld %r28, 112(%r12)
	ld %r29, 120(%r12)
	ld %r30, 128(%r12)
	ld %r31, 136(%r12)
	addi %r1, %r1, 2224
	b 21f
20:
	li %r3, 0
21:
	blr

vg_rsa_pkcs1_recover_precomputed:
	addi %r12, %r1, 0
	ld %r11, 96(%r12)
	subf %r11, %r6, %r11
	cmpldi %cr0, %r11, 0
	bne %cr0, 20f
	stdu %r1, -2224(%r1)
	addi %r12, %r1, 0
	std %r28, 112(%r12)
	std %r29, 120(%r12)
	std %r30, 128(%r12)
	std %r31, 136(%r12)
	mflr %r0
	std %r0, 144(%r12)
	or %r28, %r3, %r3
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	rlwinm %r31, %r9, 0, 0, 31
	or %r9, %r10, %r10
	or %r10, %r6, %r6
	or %r4, %r6, %r6
	ld %r0, 2328(%r12)
	std %r0, 96(%r12)
	ld %r0, 2336(%r12)
	std %r0, 104(%r12)
	ld %r5, 2344(%r12)
	ld %r6, 2352(%r12)
	addi %r3, %r12, 168
	bl {vg_rsa_public_precomputed_checked}
	addi %r12, %r1, 0
	std %r3, 152(%r12)
	addi %r4, %r12, 1192
	or %r5, %r30, %r30
	or %r6, %r31, %r31
	or %r8, %r29, %r29
	addi %r7, %r12, 168
	add %r7, %r7, %r30
	subf %r7, %r29, %r7
	addi %r9, %r6, -0
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	addi %r9, %r6, -1
	cmplwi %cr0, %r9, 0
	beq %cr0, 24f
	addi %r9, %r6, -2
	cmplwi %cr0, %r9, 0
	beq %cr0, 26f
	addi %r9, %r6, -3
	cmplwi %cr0, %r9, 0
	beq %cr0, 28f
	addi %r9, %r6, -4
	cmplwi %cr0, %r9, 0
	beq %cr0, 210f
	addi %r9, %r6, -5
	cmplwi %cr0, %r9, 0
	beq %cr0, 212f
	addi %r9, %r6, -6
	cmplwi %cr0, %r9, 0
	beq %cr0, 214f
	addi %r9, %r6, -7
	cmplwi %cr0, %r9, 0
	beq %cr0, 216f
	addi %r9, %r6, -8
	cmplwi %cr0, %r9, 0
	beq %cr0, 218f
	addi %r9, %r6, -9
	cmplwi %cr0, %r9, 0
	beq %cr0, 220f
	addi %r9, %r6, -10
	cmplwi %cr0, %r9, 0
	beq %cr0, 222f
	addi %r9, %r6, -11
	cmplwi %cr0, %r9, 0
	beq %cr0, 224f
	li %r9, 2048
	li %r10, 0
	b 225f
224:
	li %r9, 83
	li %r10, 64
225:
	b 223f
222:
	li %r9, 67
	li %r10, 48
223:
	b 221f
220:
	li %r9, 51
	li %r10, 32
221:
	b 219f
218:
	li %r9, 47
	li %r10, 28
219:
	b 217f
216:
	li %r9, 51
	li %r10, 32
217:
	b 215f
214:
	li %r9, 47
	li %r10, 28
215:
	b 213f
212:
	li %r9, 83
	li %r10, 64
213:
	b 211f
210:
	li %r9, 67
	li %r10, 48
211:
	b 29f
28:
	li %r9, 51
	li %r10, 32
29:
	b 27f
26:
	li %r9, 47
	li %r10, 28
27:
	b 25f
24:
	li %r9, 35
	li %r10, 20
25:
	b 23f
22:
	li %r9, 34
	li %r10, 16
23:
	subf %r11, %r10, %r8
	cmpldi %cr0, %r11, 0
	bne %cr0, 226f
	addi %r11, %r9, 11
	subf %r11, %r11, %r5
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	bne %cr0, 228f
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	subf %r11, %r9, %r5
	addi %r11, %r11, -3
	li %r0, 255
230:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 230b
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r9, %r6, -0
	cmplwi %cr0, %r9, 0
	beq %cr0, 231f
	addi %r9, %r6, -1
	cmplwi %cr0, %r9, 0
	beq %cr0, 233f
	addi %r9, %r6, -2
	cmplwi %cr0, %r9, 0
	beq %cr0, 235f
	addi %r9, %r6, -3
	cmplwi %cr0, %r9, 0
	beq %cr0, 237f
	addi %r9, %r6, -4
	cmplwi %cr0, %r9, 0
	beq %cr0, 239f
	addi %r9, %r6, -5
	cmplwi %cr0, %r9, 0
	beq %cr0, 241f
	addi %r9, %r6, -6
	cmplwi %cr0, %r9, 0
	beq %cr0, 243f
	addi %r9, %r6, -7
	cmplwi %cr0, %r9, 0
	beq %cr0, 245f
	addi %r9, %r6, -8
	cmplwi %cr0, %r9, 0
	beq %cr0, 247f
	addi %r9, %r6, -9
	cmplwi %cr0, %r9, 0
	beq %cr0, 249f
	addi %r9, %r6, -10
	cmplwi %cr0, %r9, 0
	beq %cr0, 251f
	addi %r9, %r6, -11
	cmplwi %cr0, %r9, 0
	beq %cr0, 253f
	b 254f
253:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 81
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 10
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 64
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
254:
	b 252f
251:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 65
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
252:
	b 250f
249:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 8
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
250:
	b 248f
247:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 7
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
248:
	b 246f
245:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
246:
	b 244f
243:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
244:
	b 242f
241:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 81
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 64
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
242:
	b 240f
239:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 65
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
240:
	b 238f
237:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
238:
	b 236f
235:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
236:
	b 234f
233:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 33
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 43
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 14
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 26
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 20
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
234:
	b 232f
231:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 12
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 8
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 42
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 247
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 16
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
232:
255:
	lbz %r0, 0(%r7)
	stb %r0, 0(%r4)
	addi %r7, %r7, 1
	addi %r4, %r4, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 255b
	li %r3, 1
	b 229f
228:
	li %r3, 0
229:
	b 227f
226:
	li %r3, 0
227:
	cmpldi %cr0, %r3, 0
	beq %cr0, 256f
	addi %r12, %r1, 0
	addi %r4, %r12, 168
	addi %r5, %r12, 1192
	or %r6, %r30, %r30
	li %r7, 0
258:
	lbz %r8, 0(%r4)
	lbz %r9, 0(%r5)
	xor %r8, %r8, %r9
	or %r7, %r7, %r8
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 258b
	addi %r8, %r7, -1
	rldicl %r8, %r8, 1, 63
	addi %r12, %r1, 0
	ld %r9, 152(%r12)
	rldicr %r9, %r9, 32, 31
	rldicl %r9, %r9, 32, 32
	li %r10, 0
	subf %r9, %r9, %r10
	rldicl %r9, %r9, 1, 63
	and %r8, %r8, %r9
	subf %r8, %r8, %r10
	std %r8, 160(%r12)
	or %r4, %r28, %r28
	or %r8, %r29, %r29
	addi %r7, %r12, 168
	add %r7, %r7, %r30
	subf %r7, %r29, %r7
259:
	lbz %r0, 0(%r7)
	stb %r0, 0(%r4)
	addi %r7, %r7, 1
	addi %r4, %r4, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 259b
	addi %r12, %r1, 0
	ld %r9, 160(%r12)
	or %r11, %r28, %r28
	or %r8, %r29, %r29
260:
	lbz %r10, 0(%r11)
	and %r10, %r10, %r9
	stb %r10, 0(%r11)
	addi %r11, %r11, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 260b
	li %r3, 1
	and %r3, %r3, %r9
	b 257f
256:
	or %r4, %r28, %r28
	or %r11, %r29, %r29
	li %r0, 0
261:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 261b
	li %r3, 0
257:
	addi %r12, %r1, 0
	ld %r0, 144(%r12)
	mtlr %r0
	ld %r28, 112(%r12)
	ld %r29, 120(%r12)
	ld %r30, 128(%r12)
	ld %r31, 136(%r12)
	addi %r1, %r1, 2224
	b 21f
20:
	or %r11, %r4, %r4
	or %r4, %r3, %r3
	li %r0, 0
262:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 262b
	li %r3, 0
21:
	blr

vg_rsa_pkcs1_sign:
	stdu %r1, -1264(%r1)
	addi %r12, %r1, 0
	std %r26, 192(%r12)
	std %r27, 200(%r12)
	std %r28, 208(%r12)
	std %r29, 216(%r12)
	std %r30, 224(%r12)
	mflr %r0
	std %r0, 232(%r12)
	or %r26, %r3, %r3
	or %r27, %r5, %r5
	or %r28, %r6, %r6
	or %r29, %r7, %r7
	or %r30, %r8, %r8
	addi %r4, %r12, 240
	or %r5, %r28, %r28
	rlwinm %r6, %r9, 0, 0, 31
	or %r7, %r10, %r10
	ld %r8, 1360(%r12)
	addi %r9, %r6, -0
	cmplwi %cr0, %r9, 0
	beq %cr0, 20f
	addi %r9, %r6, -1
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	addi %r9, %r6, -2
	cmplwi %cr0, %r9, 0
	beq %cr0, 24f
	addi %r9, %r6, -3
	cmplwi %cr0, %r9, 0
	beq %cr0, 26f
	addi %r9, %r6, -4
	cmplwi %cr0, %r9, 0
	beq %cr0, 28f
	addi %r9, %r6, -5
	cmplwi %cr0, %r9, 0
	beq %cr0, 210f
	addi %r9, %r6, -6
	cmplwi %cr0, %r9, 0
	beq %cr0, 212f
	addi %r9, %r6, -7
	cmplwi %cr0, %r9, 0
	beq %cr0, 214f
	addi %r9, %r6, -8
	cmplwi %cr0, %r9, 0
	beq %cr0, 216f
	addi %r9, %r6, -9
	cmplwi %cr0, %r9, 0
	beq %cr0, 218f
	addi %r9, %r6, -10
	cmplwi %cr0, %r9, 0
	beq %cr0, 220f
	addi %r9, %r6, -11
	cmplwi %cr0, %r9, 0
	beq %cr0, 222f
	li %r9, 2048
	li %r10, 0
	b 223f
222:
	li %r9, 83
	li %r10, 64
223:
	b 221f
220:
	li %r9, 67
	li %r10, 48
221:
	b 219f
218:
	li %r9, 51
	li %r10, 32
219:
	b 217f
216:
	li %r9, 47
	li %r10, 28
217:
	b 215f
214:
	li %r9, 51
	li %r10, 32
215:
	b 213f
212:
	li %r9, 47
	li %r10, 28
213:
	b 211f
210:
	li %r9, 83
	li %r10, 64
211:
	b 29f
28:
	li %r9, 67
	li %r10, 48
29:
	b 27f
26:
	li %r9, 51
	li %r10, 32
27:
	b 25f
24:
	li %r9, 47
	li %r10, 28
25:
	b 23f
22:
	li %r9, 35
	li %r10, 20
23:
	b 21f
20:
	li %r9, 34
	li %r10, 16
21:
	subf %r11, %r10, %r8
	cmpldi %cr0, %r11, 0
	bne %cr0, 224f
	addi %r11, %r9, 11
	subf %r11, %r11, %r5
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	bne %cr0, 226f
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	subf %r11, %r9, %r5
	addi %r11, %r11, -3
	li %r0, 255
228:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 228b
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r9, %r6, -0
	cmplwi %cr0, %r9, 0
	beq %cr0, 229f
	addi %r9, %r6, -1
	cmplwi %cr0, %r9, 0
	beq %cr0, 231f
	addi %r9, %r6, -2
	cmplwi %cr0, %r9, 0
	beq %cr0, 233f
	addi %r9, %r6, -3
	cmplwi %cr0, %r9, 0
	beq %cr0, 235f
	addi %r9, %r6, -4
	cmplwi %cr0, %r9, 0
	beq %cr0, 237f
	addi %r9, %r6, -5
	cmplwi %cr0, %r9, 0
	beq %cr0, 239f
	addi %r9, %r6, -6
	cmplwi %cr0, %r9, 0
	beq %cr0, 241f
	addi %r9, %r6, -7
	cmplwi %cr0, %r9, 0
	beq %cr0, 243f
	addi %r9, %r6, -8
	cmplwi %cr0, %r9, 0
	beq %cr0, 245f
	addi %r9, %r6, -9
	cmplwi %cr0, %r9, 0
	beq %cr0, 247f
	addi %r9, %r6, -10
	cmplwi %cr0, %r9, 0
	beq %cr0, 249f
	addi %r9, %r6, -11
	cmplwi %cr0, %r9, 0
	beq %cr0, 251f
	b 252f
251:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 81
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 10
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 64
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
252:
	b 250f
249:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 65
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
250:
	b 248f
247:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 8
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
248:
	b 246f
245:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 7
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
246:
	b 244f
243:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
244:
	b 242f
241:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
242:
	b 240f
239:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 81
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 64
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
240:
	b 238f
237:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 65
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
238:
	b 236f
235:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 49
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
236:
	b 234f
233:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 45
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 96
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 101
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 28
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
234:
	b 232f
231:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 33
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 9
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 43
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 14
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 3
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 26
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 20
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
232:
	b 230f
229:
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 32
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 48
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 12
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 6
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 8
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 42
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 72
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 134
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 247
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 13
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 2
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 5
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 0
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 4
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	li %r0, 16
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
230:
253:
	lbz %r0, 0(%r7)
	stb %r0, 0(%r4)
	addi %r7, %r7, 1
	addi %r4, %r4, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 253b
	li %r3, 1
	b 227f
226:
	li %r3, 0
227:
	b 225f
224:
	li %r3, 0
225:
	cmpldi %cr0, %r3, 0
	beq %cr0, 254f
	addi %r12, %r1, 0
	ld %r0, 1368(%r12)
	std %r0, 96(%r12)
	ld %r0, 1376(%r12)
	std %r0, 104(%r12)
	ld %r0, 1384(%r12)
	std %r0, 112(%r12)
	ld %r0, 1392(%r12)
	std %r0, 120(%r12)
	ld %r0, 1400(%r12)
	std %r0, 128(%r12)
	ld %r0, 1408(%r12)
	std %r0, 136(%r12)
	ld %r0, 1416(%r12)
	std %r0, 144(%r12)
	ld %r0, 1424(%r12)
	std %r0, 152(%r12)
	ld %r0, 1432(%r12)
	std %r0, 160(%r12)
	ld %r0, 1440(%r12)
	std %r0, 168(%r12)
	ld %r0, 1448(%r12)
	std %r0, 176(%r12)
	ld %r0, 1456(%r12)
	std %r0, 184(%r12)
	or %r3, %r26, %r26
	or %r4, %r28, %r28
	or %r5, %r27, %r27
	or %r6, %r28, %r28
	or %r7, %r29, %r29
	or %r8, %r30, %r30
	addi %r9, %r12, 240
	or %r10, %r28, %r28
	bl {vg_rsa_private_checked}
	addi %r12, %r1, 0
	addi %r7, %r12, 240
	or %r8, %r28, %r28
	li %r0, 0
256:
	stb %r0, 0(%r7)
	addi %r7, %r7, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 256b
	b 255f
254:
	or %r7, %r26, %r26
	or %r8, %r28, %r28
	li %r0, 0
257:
	stb %r0, 0(%r7)
	addi %r7, %r7, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 257b
255:
	addi %r12, %r1, 0
	ld %r0, 232(%r12)
	mtlr %r0
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	addi %r1, %r1, 1264
	blr
