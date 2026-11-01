// The functions of `src/internal/vg_mldsa_hint_bit_unpack.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_unpack:
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	subf %r12, %r5, %r4
	addi %r9, %r7, 0
	li %r0, 0
	addi %r10, %r6, 0
20:
	stw %r0, 0(%r10)
	addi %r10, %r10, 4
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 20b
	li %r11, 0
	add %r10, %r3, %r5
21:
	subf %r0, %r11, %r5
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	b 23f
22:
	lbz %r8, 0(%r10)
	subf %r0, %r11, %r8
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	li %r11, 256
	b 25f
24:
	subf %r0, %r8, %r5
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 26f
	li %r11, 256
	b 27f
26:
	subf %r0, %r8, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 28f
	add %r9, %r3, %r11
	lbz %r9, 0(%r9)
	rldicr %r9, %r9, 2, 61
	add %r9, %r6, %r9
	li %r0, 1
	stw %r0, 0(%r9)
	addi %r11, %r11, 1
	subf %r0, %r8, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 210f
212:
	add %r9, %r3, %r11
	lbz %r0, 0(%r9)
	addi %r9, %r9, -1
	lbz %r9, 0(%r9)
	subf %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 213f
	add %r9, %r3, %r11
	lbz %r9, 0(%r9)
	rldicr %r9, %r9, 2, 61
	add %r9, %r6, %r9
	li %r0, 1
	stw %r0, 0(%r9)
	addi %r11, %r11, 1
	b 214f
213:
	li %r11, 256
214:
	subf %r0, %r8, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	bne %cr0, 212b
	b 211f
210:
211:
	b 29f
28:
29:
27:
25:
23:
	addi %r10, %r10, 1
	addi %r6, %r6, 1024
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	subf %r0, %r5, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 215f
217:
	add %r9, %r3, %r11
	lbz %r9, 0(%r9)
	cmpldi %cr0, %r9, 0
	beq %cr0, 218f
	li %r11, 256
	b 219f
218:
	addi %r11, %r11, 1
219:
	subf %r0, %r5, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	bne %cr0, 217b
	b 216f
215:
216:
	subf %r0, %r11, %r5
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	subf %r3, %r0, %r3
	blr
