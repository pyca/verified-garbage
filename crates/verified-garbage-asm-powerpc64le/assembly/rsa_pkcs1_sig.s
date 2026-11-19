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
	li %r0, 0
	stdu %r1, -2224(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	std %r0, 720(%r12)
	std %r0, 728(%r12)
	std %r0, 736(%r12)
	std %r0, 744(%r12)
	std %r0, 752(%r12)
	std %r0, 760(%r12)
	std %r0, 768(%r12)
	std %r0, 776(%r12)
	std %r0, 784(%r12)
	std %r0, 792(%r12)
	std %r0, 800(%r12)
	std %r0, 808(%r12)
	std %r0, 816(%r12)
	std %r0, 824(%r12)
	std %r0, 832(%r12)
	std %r0, 840(%r12)
	std %r0, 848(%r12)
	std %r0, 856(%r12)
	std %r0, 864(%r12)
	std %r0, 872(%r12)
	std %r0, 880(%r12)
	std %r0, 888(%r12)
	std %r0, 896(%r12)
	std %r0, 904(%r12)
	std %r0, 912(%r12)
	std %r0, 920(%r12)
	std %r0, 928(%r12)
	std %r0, 936(%r12)
	std %r0, 944(%r12)
	std %r0, 952(%r12)
	std %r0, 960(%r12)
	std %r0, 968(%r12)
	std %r0, 976(%r12)
	std %r0, 984(%r12)
	std %r0, 992(%r12)
	std %r0, 1000(%r12)
	std %r0, 1008(%r12)
	std %r0, 1016(%r12)
	std %r0, 1024(%r12)
	std %r0, 1032(%r12)
	std %r0, 1040(%r12)
	std %r0, 1048(%r12)
	std %r0, 1056(%r12)
	std %r0, 1064(%r12)
	std %r0, 1072(%r12)
	std %r0, 1080(%r12)
	std %r0, 1088(%r12)
	std %r0, 1096(%r12)
	std %r0, 1104(%r12)
	std %r0, 1112(%r12)
	std %r0, 1120(%r12)
	std %r0, 1128(%r12)
	std %r0, 1136(%r12)
	std %r0, 1144(%r12)
	std %r0, 1152(%r12)
	std %r0, 1160(%r12)
	std %r0, 1168(%r12)
	std %r0, 1176(%r12)
	std %r0, 1184(%r12)
	std %r0, 1192(%r12)
	std %r0, 1200(%r12)
	std %r0, 1208(%r12)
	std %r0, 1216(%r12)
	std %r0, 1224(%r12)
	std %r0, 1232(%r12)
	std %r0, 1240(%r12)
	std %r0, 1248(%r12)
	std %r0, 1256(%r12)
	std %r0, 1264(%r12)
	std %r0, 1272(%r12)
	std %r0, 1280(%r12)
	std %r0, 1288(%r12)
	std %r0, 1296(%r12)
	std %r0, 1304(%r12)
	std %r0, 1312(%r12)
	std %r0, 1320(%r12)
	std %r0, 1328(%r12)
	std %r0, 1336(%r12)
	std %r0, 1344(%r12)
	std %r0, 1352(%r12)
	std %r0, 1360(%r12)
	std %r0, 1368(%r12)
	std %r0, 1376(%r12)
	std %r0, 1384(%r12)
	std %r0, 1392(%r12)
	std %r0, 1400(%r12)
	std %r0, 1408(%r12)
	std %r0, 1416(%r12)
	std %r0, 1424(%r12)
	std %r0, 1432(%r12)
	std %r0, 1440(%r12)
	std %r0, 1448(%r12)
	std %r0, 1456(%r12)
	std %r0, 1464(%r12)
	std %r0, 1472(%r12)
	std %r0, 1480(%r12)
	std %r0, 1488(%r12)
	std %r0, 1496(%r12)
	std %r0, 1504(%r12)
	std %r0, 1512(%r12)
	std %r0, 1520(%r12)
	std %r0, 1528(%r12)
	std %r0, 1536(%r12)
	std %r0, 1544(%r12)
	std %r0, 1552(%r12)
	std %r0, 1560(%r12)
	std %r0, 1568(%r12)
	std %r0, 1576(%r12)
	std %r0, 1584(%r12)
	std %r0, 1592(%r12)
	std %r0, 1600(%r12)
	std %r0, 1608(%r12)
	std %r0, 1616(%r12)
	std %r0, 1624(%r12)
	std %r0, 1632(%r12)
	std %r0, 1640(%r12)
	std %r0, 1648(%r12)
	std %r0, 1656(%r12)
	std %r0, 1664(%r12)
	std %r0, 1672(%r12)
	std %r0, 1680(%r12)
	std %r0, 1688(%r12)
	std %r0, 1696(%r12)
	std %r0, 1704(%r12)
	std %r0, 1712(%r12)
	std %r0, 1720(%r12)
	std %r0, 1728(%r12)
	std %r0, 1736(%r12)
	std %r0, 1744(%r12)
	std %r0, 1752(%r12)
	std %r0, 1760(%r12)
	std %r0, 1768(%r12)
	std %r0, 1776(%r12)
	std %r0, 1784(%r12)
	std %r0, 1792(%r12)
	std %r0, 1800(%r12)
	std %r0, 1808(%r12)
	std %r0, 1816(%r12)
	std %r0, 1824(%r12)
	std %r0, 1832(%r12)
	std %r0, 1840(%r12)
	std %r0, 1848(%r12)
	std %r0, 1856(%r12)
	std %r0, 1864(%r12)
	std %r0, 1872(%r12)
	std %r0, 1880(%r12)
	std %r0, 1888(%r12)
	std %r0, 1896(%r12)
	std %r0, 1904(%r12)
	std %r0, 1912(%r12)
	std %r0, 1920(%r12)
	std %r0, 1928(%r12)
	std %r0, 1936(%r12)
	std %r0, 1944(%r12)
	std %r0, 1952(%r12)
	std %r0, 1960(%r12)
	std %r0, 1968(%r12)
	std %r0, 1976(%r12)
	std %r0, 1984(%r12)
	std %r0, 1992(%r12)
	std %r0, 2000(%r12)
	std %r0, 2008(%r12)
	std %r0, 2016(%r12)
	std %r0, 2024(%r12)
	std %r0, 2032(%r12)
	std %r0, 2040(%r12)
	std %r0, 2048(%r12)
	std %r0, 2056(%r12)
	std %r0, 2064(%r12)
	std %r0, 2072(%r12)
	std %r0, 2080(%r12)
	std %r0, 2088(%r12)
	std %r0, 2096(%r12)
	std %r0, 2104(%r12)
	std %r0, 2112(%r12)
	std %r0, 2120(%r12)
	std %r0, 2128(%r12)
	std %r0, 2136(%r12)
	std %r0, 2144(%r12)
	std %r0, 2152(%r12)
	std %r0, 2160(%r12)
	std %r0, 2168(%r12)
	std %r0, 2176(%r12)
	std %r0, 2184(%r12)
	addi %r1, %r1, 2224
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
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
	li %r0, 0
	stdu %r1, -2224(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	std %r0, 720(%r12)
	std %r0, 728(%r12)
	std %r0, 736(%r12)
	std %r0, 744(%r12)
	std %r0, 752(%r12)
	std %r0, 760(%r12)
	std %r0, 768(%r12)
	std %r0, 776(%r12)
	std %r0, 784(%r12)
	std %r0, 792(%r12)
	std %r0, 800(%r12)
	std %r0, 808(%r12)
	std %r0, 816(%r12)
	std %r0, 824(%r12)
	std %r0, 832(%r12)
	std %r0, 840(%r12)
	std %r0, 848(%r12)
	std %r0, 856(%r12)
	std %r0, 864(%r12)
	std %r0, 872(%r12)
	std %r0, 880(%r12)
	std %r0, 888(%r12)
	std %r0, 896(%r12)
	std %r0, 904(%r12)
	std %r0, 912(%r12)
	std %r0, 920(%r12)
	std %r0, 928(%r12)
	std %r0, 936(%r12)
	std %r0, 944(%r12)
	std %r0, 952(%r12)
	std %r0, 960(%r12)
	std %r0, 968(%r12)
	std %r0, 976(%r12)
	std %r0, 984(%r12)
	std %r0, 992(%r12)
	std %r0, 1000(%r12)
	std %r0, 1008(%r12)
	std %r0, 1016(%r12)
	std %r0, 1024(%r12)
	std %r0, 1032(%r12)
	std %r0, 1040(%r12)
	std %r0, 1048(%r12)
	std %r0, 1056(%r12)
	std %r0, 1064(%r12)
	std %r0, 1072(%r12)
	std %r0, 1080(%r12)
	std %r0, 1088(%r12)
	std %r0, 1096(%r12)
	std %r0, 1104(%r12)
	std %r0, 1112(%r12)
	std %r0, 1120(%r12)
	std %r0, 1128(%r12)
	std %r0, 1136(%r12)
	std %r0, 1144(%r12)
	std %r0, 1152(%r12)
	std %r0, 1160(%r12)
	std %r0, 1168(%r12)
	std %r0, 1176(%r12)
	std %r0, 1184(%r12)
	std %r0, 1192(%r12)
	std %r0, 1200(%r12)
	std %r0, 1208(%r12)
	std %r0, 1216(%r12)
	std %r0, 1224(%r12)
	std %r0, 1232(%r12)
	std %r0, 1240(%r12)
	std %r0, 1248(%r12)
	std %r0, 1256(%r12)
	std %r0, 1264(%r12)
	std %r0, 1272(%r12)
	std %r0, 1280(%r12)
	std %r0, 1288(%r12)
	std %r0, 1296(%r12)
	std %r0, 1304(%r12)
	std %r0, 1312(%r12)
	std %r0, 1320(%r12)
	std %r0, 1328(%r12)
	std %r0, 1336(%r12)
	std %r0, 1344(%r12)
	std %r0, 1352(%r12)
	std %r0, 1360(%r12)
	std %r0, 1368(%r12)
	std %r0, 1376(%r12)
	std %r0, 1384(%r12)
	std %r0, 1392(%r12)
	std %r0, 1400(%r12)
	std %r0, 1408(%r12)
	std %r0, 1416(%r12)
	std %r0, 1424(%r12)
	std %r0, 1432(%r12)
	std %r0, 1440(%r12)
	std %r0, 1448(%r12)
	std %r0, 1456(%r12)
	std %r0, 1464(%r12)
	std %r0, 1472(%r12)
	std %r0, 1480(%r12)
	std %r0, 1488(%r12)
	std %r0, 1496(%r12)
	std %r0, 1504(%r12)
	std %r0, 1512(%r12)
	std %r0, 1520(%r12)
	std %r0, 1528(%r12)
	std %r0, 1536(%r12)
	std %r0, 1544(%r12)
	std %r0, 1552(%r12)
	std %r0, 1560(%r12)
	std %r0, 1568(%r12)
	std %r0, 1576(%r12)
	std %r0, 1584(%r12)
	std %r0, 1592(%r12)
	std %r0, 1600(%r12)
	std %r0, 1608(%r12)
	std %r0, 1616(%r12)
	std %r0, 1624(%r12)
	std %r0, 1632(%r12)
	std %r0, 1640(%r12)
	std %r0, 1648(%r12)
	std %r0, 1656(%r12)
	std %r0, 1664(%r12)
	std %r0, 1672(%r12)
	std %r0, 1680(%r12)
	std %r0, 1688(%r12)
	std %r0, 1696(%r12)
	std %r0, 1704(%r12)
	std %r0, 1712(%r12)
	std %r0, 1720(%r12)
	std %r0, 1728(%r12)
	std %r0, 1736(%r12)
	std %r0, 1744(%r12)
	std %r0, 1752(%r12)
	std %r0, 1760(%r12)
	std %r0, 1768(%r12)
	std %r0, 1776(%r12)
	std %r0, 1784(%r12)
	std %r0, 1792(%r12)
	std %r0, 1800(%r12)
	std %r0, 1808(%r12)
	std %r0, 1816(%r12)
	std %r0, 1824(%r12)
	std %r0, 1832(%r12)
	std %r0, 1840(%r12)
	std %r0, 1848(%r12)
	std %r0, 1856(%r12)
	std %r0, 1864(%r12)
	std %r0, 1872(%r12)
	std %r0, 1880(%r12)
	std %r0, 1888(%r12)
	std %r0, 1896(%r12)
	std %r0, 1904(%r12)
	std %r0, 1912(%r12)
	std %r0, 1920(%r12)
	std %r0, 1928(%r12)
	std %r0, 1936(%r12)
	std %r0, 1944(%r12)
	std %r0, 1952(%r12)
	std %r0, 1960(%r12)
	std %r0, 1968(%r12)
	std %r0, 1976(%r12)
	std %r0, 1984(%r12)
	std %r0, 1992(%r12)
	std %r0, 2000(%r12)
	std %r0, 2008(%r12)
	std %r0, 2016(%r12)
	std %r0, 2024(%r12)
	std %r0, 2032(%r12)
	std %r0, 2040(%r12)
	std %r0, 2048(%r12)
	std %r0, 2056(%r12)
	std %r0, 2064(%r12)
	std %r0, 2072(%r12)
	std %r0, 2080(%r12)
	std %r0, 2088(%r12)
	std %r0, 2096(%r12)
	std %r0, 2104(%r12)
	std %r0, 2112(%r12)
	std %r0, 2120(%r12)
	std %r0, 2128(%r12)
	std %r0, 2136(%r12)
	std %r0, 2144(%r12)
	std %r0, 2152(%r12)
	std %r0, 2160(%r12)
	std %r0, 2168(%r12)
	std %r0, 2176(%r12)
	std %r0, 2184(%r12)
	addi %r1, %r1, 2224
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	blr

vg_rsa_pkcs1_sign_precomputed:
	stdu %r1, -1280(%r1)
	addi %r12, %r1, 0
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	std %r30, 240(%r12)
	mflr %r0
	std %r0, 248(%r12)
	or %r26, %r3, %r3
	or %r27, %r5, %r5
	or %r28, %r6, %r6
	or %r29, %r7, %r7
	or %r30, %r8, %r8
	addi %r4, %r12, 256
	or %r5, %r28, %r28
	rlwinm %r6, %r9, 0, 0, 31
	or %r7, %r10, %r10
	ld %r8, 1376(%r12)
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
	ld %r0, 1384(%r12)
	std %r0, 96(%r12)
	ld %r0, 1392(%r12)
	std %r0, 104(%r12)
	ld %r0, 1400(%r12)
	std %r0, 112(%r12)
	ld %r0, 1408(%r12)
	std %r0, 120(%r12)
	ld %r0, 1416(%r12)
	std %r0, 128(%r12)
	ld %r0, 1424(%r12)
	std %r0, 136(%r12)
	ld %r0, 1432(%r12)
	std %r0, 144(%r12)
	ld %r0, 1440(%r12)
	std %r0, 152(%r12)
	ld %r0, 1448(%r12)
	std %r0, 160(%r12)
	ld %r0, 1456(%r12)
	std %r0, 168(%r12)
	ld %r0, 1464(%r12)
	std %r0, 176(%r12)
	ld %r0, 1472(%r12)
	std %r0, 184(%r12)
	ld %r0, 1480(%r12)
	std %r0, 192(%r12)
	ld %r0, 1488(%r12)
	std %r0, 200(%r12)
	or %r3, %r26, %r26
	or %r4, %r28, %r28
	or %r5, %r27, %r27
	or %r6, %r28, %r28
	or %r7, %r29, %r29
	or %r8, %r30, %r30
	addi %r9, %r12, 256
	or %r10, %r28, %r28
	bl {vg_rsa_private_checked_precomputed}
	addi %r12, %r1, 0
	addi %r7, %r12, 256
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
	ld %r0, 248(%r12)
	mtlr %r0
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
	ld %r30, 240(%r12)
	addi %r1, %r1, 1280
	li %r0, 0
	stdu %r1, -4064(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	std %r0, 720(%r12)
	std %r0, 728(%r12)
	std %r0, 736(%r12)
	std %r0, 744(%r12)
	std %r0, 752(%r12)
	std %r0, 760(%r12)
	std %r0, 768(%r12)
	std %r0, 776(%r12)
	std %r0, 784(%r12)
	std %r0, 792(%r12)
	std %r0, 800(%r12)
	std %r0, 808(%r12)
	std %r0, 816(%r12)
	std %r0, 824(%r12)
	std %r0, 832(%r12)
	std %r0, 840(%r12)
	std %r0, 848(%r12)
	std %r0, 856(%r12)
	std %r0, 864(%r12)
	std %r0, 872(%r12)
	std %r0, 880(%r12)
	std %r0, 888(%r12)
	std %r0, 896(%r12)
	std %r0, 904(%r12)
	std %r0, 912(%r12)
	std %r0, 920(%r12)
	std %r0, 928(%r12)
	std %r0, 936(%r12)
	std %r0, 944(%r12)
	std %r0, 952(%r12)
	std %r0, 960(%r12)
	std %r0, 968(%r12)
	std %r0, 976(%r12)
	std %r0, 984(%r12)
	std %r0, 992(%r12)
	std %r0, 1000(%r12)
	std %r0, 1008(%r12)
	std %r0, 1016(%r12)
	std %r0, 1024(%r12)
	std %r0, 1032(%r12)
	std %r0, 1040(%r12)
	std %r0, 1048(%r12)
	std %r0, 1056(%r12)
	std %r0, 1064(%r12)
	std %r0, 1072(%r12)
	std %r0, 1080(%r12)
	std %r0, 1088(%r12)
	std %r0, 1096(%r12)
	std %r0, 1104(%r12)
	std %r0, 1112(%r12)
	std %r0, 1120(%r12)
	std %r0, 1128(%r12)
	std %r0, 1136(%r12)
	std %r0, 1144(%r12)
	std %r0, 1152(%r12)
	std %r0, 1160(%r12)
	std %r0, 1168(%r12)
	std %r0, 1176(%r12)
	std %r0, 1184(%r12)
	std %r0, 1192(%r12)
	std %r0, 1200(%r12)
	std %r0, 1208(%r12)
	std %r0, 1216(%r12)
	std %r0, 1224(%r12)
	std %r0, 1232(%r12)
	std %r0, 1240(%r12)
	std %r0, 1248(%r12)
	std %r0, 1256(%r12)
	std %r0, 1264(%r12)
	std %r0, 1272(%r12)
	std %r0, 1280(%r12)
	std %r0, 1288(%r12)
	std %r0, 1296(%r12)
	std %r0, 1304(%r12)
	std %r0, 1312(%r12)
	std %r0, 1320(%r12)
	std %r0, 1328(%r12)
	std %r0, 1336(%r12)
	std %r0, 1344(%r12)
	std %r0, 1352(%r12)
	std %r0, 1360(%r12)
	std %r0, 1368(%r12)
	std %r0, 1376(%r12)
	std %r0, 1384(%r12)
	std %r0, 1392(%r12)
	std %r0, 1400(%r12)
	std %r0, 1408(%r12)
	std %r0, 1416(%r12)
	std %r0, 1424(%r12)
	std %r0, 1432(%r12)
	std %r0, 1440(%r12)
	std %r0, 1448(%r12)
	std %r0, 1456(%r12)
	std %r0, 1464(%r12)
	std %r0, 1472(%r12)
	std %r0, 1480(%r12)
	std %r0, 1488(%r12)
	std %r0, 1496(%r12)
	std %r0, 1504(%r12)
	std %r0, 1512(%r12)
	std %r0, 1520(%r12)
	std %r0, 1528(%r12)
	std %r0, 1536(%r12)
	std %r0, 1544(%r12)
	std %r0, 1552(%r12)
	std %r0, 1560(%r12)
	std %r0, 1568(%r12)
	std %r0, 1576(%r12)
	std %r0, 1584(%r12)
	std %r0, 1592(%r12)
	std %r0, 1600(%r12)
	std %r0, 1608(%r12)
	std %r0, 1616(%r12)
	std %r0, 1624(%r12)
	std %r0, 1632(%r12)
	std %r0, 1640(%r12)
	std %r0, 1648(%r12)
	std %r0, 1656(%r12)
	std %r0, 1664(%r12)
	std %r0, 1672(%r12)
	std %r0, 1680(%r12)
	std %r0, 1688(%r12)
	std %r0, 1696(%r12)
	std %r0, 1704(%r12)
	std %r0, 1712(%r12)
	std %r0, 1720(%r12)
	std %r0, 1728(%r12)
	std %r0, 1736(%r12)
	std %r0, 1744(%r12)
	std %r0, 1752(%r12)
	std %r0, 1760(%r12)
	std %r0, 1768(%r12)
	std %r0, 1776(%r12)
	std %r0, 1784(%r12)
	std %r0, 1792(%r12)
	std %r0, 1800(%r12)
	std %r0, 1808(%r12)
	std %r0, 1816(%r12)
	std %r0, 1824(%r12)
	std %r0, 1832(%r12)
	std %r0, 1840(%r12)
	std %r0, 1848(%r12)
	std %r0, 1856(%r12)
	std %r0, 1864(%r12)
	std %r0, 1872(%r12)
	std %r0, 1880(%r12)
	std %r0, 1888(%r12)
	std %r0, 1896(%r12)
	std %r0, 1904(%r12)
	std %r0, 1912(%r12)
	std %r0, 1920(%r12)
	std %r0, 1928(%r12)
	std %r0, 1936(%r12)
	std %r0, 1944(%r12)
	std %r0, 1952(%r12)
	std %r0, 1960(%r12)
	std %r0, 1968(%r12)
	std %r0, 1976(%r12)
	std %r0, 1984(%r12)
	std %r0, 1992(%r12)
	std %r0, 2000(%r12)
	std %r0, 2008(%r12)
	std %r0, 2016(%r12)
	std %r0, 2024(%r12)
	std %r0, 2032(%r12)
	std %r0, 2040(%r12)
	std %r0, 2048(%r12)
	std %r0, 2056(%r12)
	std %r0, 2064(%r12)
	std %r0, 2072(%r12)
	std %r0, 2080(%r12)
	std %r0, 2088(%r12)
	std %r0, 2096(%r12)
	std %r0, 2104(%r12)
	std %r0, 2112(%r12)
	std %r0, 2120(%r12)
	std %r0, 2128(%r12)
	std %r0, 2136(%r12)
	std %r0, 2144(%r12)
	std %r0, 2152(%r12)
	std %r0, 2160(%r12)
	std %r0, 2168(%r12)
	std %r0, 2176(%r12)
	std %r0, 2184(%r12)
	std %r0, 2192(%r12)
	std %r0, 2200(%r12)
	std %r0, 2208(%r12)
	std %r0, 2216(%r12)
	std %r0, 2224(%r12)
	std %r0, 2232(%r12)
	std %r0, 2240(%r12)
	std %r0, 2248(%r12)
	std %r0, 2256(%r12)
	std %r0, 2264(%r12)
	std %r0, 2272(%r12)
	std %r0, 2280(%r12)
	std %r0, 2288(%r12)
	std %r0, 2296(%r12)
	std %r0, 2304(%r12)
	std %r0, 2312(%r12)
	std %r0, 2320(%r12)
	std %r0, 2328(%r12)
	std %r0, 2336(%r12)
	std %r0, 2344(%r12)
	std %r0, 2352(%r12)
	std %r0, 2360(%r12)
	std %r0, 2368(%r12)
	std %r0, 2376(%r12)
	std %r0, 2384(%r12)
	std %r0, 2392(%r12)
	std %r0, 2400(%r12)
	std %r0, 2408(%r12)
	std %r0, 2416(%r12)
	std %r0, 2424(%r12)
	std %r0, 2432(%r12)
	std %r0, 2440(%r12)
	std %r0, 2448(%r12)
	std %r0, 2456(%r12)
	std %r0, 2464(%r12)
	std %r0, 2472(%r12)
	std %r0, 2480(%r12)
	std %r0, 2488(%r12)
	std %r0, 2496(%r12)
	std %r0, 2504(%r12)
	std %r0, 2512(%r12)
	std %r0, 2520(%r12)
	std %r0, 2528(%r12)
	std %r0, 2536(%r12)
	std %r0, 2544(%r12)
	std %r0, 2552(%r12)
	std %r0, 2560(%r12)
	std %r0, 2568(%r12)
	std %r0, 2576(%r12)
	std %r0, 2584(%r12)
	std %r0, 2592(%r12)
	std %r0, 2600(%r12)
	std %r0, 2608(%r12)
	std %r0, 2616(%r12)
	std %r0, 2624(%r12)
	std %r0, 2632(%r12)
	std %r0, 2640(%r12)
	std %r0, 2648(%r12)
	std %r0, 2656(%r12)
	std %r0, 2664(%r12)
	std %r0, 2672(%r12)
	std %r0, 2680(%r12)
	std %r0, 2688(%r12)
	std %r0, 2696(%r12)
	std %r0, 2704(%r12)
	std %r0, 2712(%r12)
	std %r0, 2720(%r12)
	std %r0, 2728(%r12)
	std %r0, 2736(%r12)
	std %r0, 2744(%r12)
	std %r0, 2752(%r12)
	std %r0, 2760(%r12)
	std %r0, 2768(%r12)
	std %r0, 2776(%r12)
	std %r0, 2784(%r12)
	std %r0, 2792(%r12)
	std %r0, 2800(%r12)
	std %r0, 2808(%r12)
	std %r0, 2816(%r12)
	std %r0, 2824(%r12)
	std %r0, 2832(%r12)
	std %r0, 2840(%r12)
	std %r0, 2848(%r12)
	std %r0, 2856(%r12)
	std %r0, 2864(%r12)
	std %r0, 2872(%r12)
	std %r0, 2880(%r12)
	std %r0, 2888(%r12)
	std %r0, 2896(%r12)
	std %r0, 2904(%r12)
	std %r0, 2912(%r12)
	std %r0, 2920(%r12)
	std %r0, 2928(%r12)
	std %r0, 2936(%r12)
	std %r0, 2944(%r12)
	std %r0, 2952(%r12)
	std %r0, 2960(%r12)
	std %r0, 2968(%r12)
	std %r0, 2976(%r12)
	std %r0, 2984(%r12)
	std %r0, 2992(%r12)
	std %r0, 3000(%r12)
	std %r0, 3008(%r12)
	std %r0, 3016(%r12)
	std %r0, 3024(%r12)
	std %r0, 3032(%r12)
	std %r0, 3040(%r12)
	std %r0, 3048(%r12)
	std %r0, 3056(%r12)
	std %r0, 3064(%r12)
	std %r0, 3072(%r12)
	std %r0, 3080(%r12)
	std %r0, 3088(%r12)
	std %r0, 3096(%r12)
	std %r0, 3104(%r12)
	std %r0, 3112(%r12)
	std %r0, 3120(%r12)
	std %r0, 3128(%r12)
	std %r0, 3136(%r12)
	std %r0, 3144(%r12)
	std %r0, 3152(%r12)
	std %r0, 3160(%r12)
	std %r0, 3168(%r12)
	std %r0, 3176(%r12)
	std %r0, 3184(%r12)
	std %r0, 3192(%r12)
	std %r0, 3200(%r12)
	std %r0, 3208(%r12)
	std %r0, 3216(%r12)
	std %r0, 3224(%r12)
	std %r0, 3232(%r12)
	std %r0, 3240(%r12)
	std %r0, 3248(%r12)
	std %r0, 3256(%r12)
	std %r0, 3264(%r12)
	std %r0, 3272(%r12)
	std %r0, 3280(%r12)
	std %r0, 3288(%r12)
	std %r0, 3296(%r12)
	std %r0, 3304(%r12)
	std %r0, 3312(%r12)
	std %r0, 3320(%r12)
	std %r0, 3328(%r12)
	std %r0, 3336(%r12)
	std %r0, 3344(%r12)
	std %r0, 3352(%r12)
	std %r0, 3360(%r12)
	std %r0, 3368(%r12)
	std %r0, 3376(%r12)
	std %r0, 3384(%r12)
	std %r0, 3392(%r12)
	std %r0, 3400(%r12)
	std %r0, 3408(%r12)
	std %r0, 3416(%r12)
	std %r0, 3424(%r12)
	std %r0, 3432(%r12)
	std %r0, 3440(%r12)
	std %r0, 3448(%r12)
	std %r0, 3456(%r12)
	std %r0, 3464(%r12)
	std %r0, 3472(%r12)
	std %r0, 3480(%r12)
	std %r0, 3488(%r12)
	std %r0, 3496(%r12)
	std %r0, 3504(%r12)
	std %r0, 3512(%r12)
	std %r0, 3520(%r12)
	std %r0, 3528(%r12)
	std %r0, 3536(%r12)
	std %r0, 3544(%r12)
	std %r0, 3552(%r12)
	std %r0, 3560(%r12)
	std %r0, 3568(%r12)
	std %r0, 3576(%r12)
	std %r0, 3584(%r12)
	std %r0, 3592(%r12)
	std %r0, 3600(%r12)
	std %r0, 3608(%r12)
	std %r0, 3616(%r12)
	std %r0, 3624(%r12)
	std %r0, 3632(%r12)
	std %r0, 3640(%r12)
	std %r0, 3648(%r12)
	std %r0, 3656(%r12)
	std %r0, 3664(%r12)
	std %r0, 3672(%r12)
	std %r0, 3680(%r12)
	std %r0, 3688(%r12)
	std %r0, 3696(%r12)
	std %r0, 3704(%r12)
	std %r0, 3712(%r12)
	std %r0, 3720(%r12)
	std %r0, 3728(%r12)
	std %r0, 3736(%r12)
	std %r0, 3744(%r12)
	std %r0, 3752(%r12)
	std %r0, 3760(%r12)
	std %r0, 3768(%r12)
	std %r0, 3776(%r12)
	std %r0, 3784(%r12)
	std %r0, 3792(%r12)
	std %r0, 3800(%r12)
	std %r0, 3808(%r12)
	std %r0, 3816(%r12)
	std %r0, 3824(%r12)
	std %r0, 3832(%r12)
	std %r0, 3840(%r12)
	std %r0, 3848(%r12)
	std %r0, 3856(%r12)
	std %r0, 3864(%r12)
	std %r0, 3872(%r12)
	std %r0, 3880(%r12)
	std %r0, 3888(%r12)
	std %r0, 3896(%r12)
	std %r0, 3904(%r12)
	std %r0, 3912(%r12)
	std %r0, 3920(%r12)
	std %r0, 3928(%r12)
	std %r0, 3936(%r12)
	std %r0, 3944(%r12)
	std %r0, 3952(%r12)
	std %r0, 3960(%r12)
	std %r0, 3968(%r12)
	std %r0, 3976(%r12)
	std %r0, 3984(%r12)
	std %r0, 3992(%r12)
	std %r0, 4000(%r12)
	std %r0, 4008(%r12)
	std %r0, 4016(%r12)
	std %r0, 4024(%r12)
	addi %r1, %r1, 4064
	stdu %r1, -4032(%r1)
	stdu %r1, -576(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	addi %r1, %r1, 576
	addi %r1, %r1, 4032
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	blr
