// The functions of `src/internal/vg_p192_inv_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_inv_mod_n:
	mflr %r0
	std %r0, 1152(%r3)
	ld %r4, 952(%r3)
	std %r4, 472(%r3)
	ld %r4, 960(%r3)
	std %r4, 480(%r3)
	ld %r4, 968(%r3)
	std %r4, 488(%r3)
	li %r4, 664
	li %r5, 952
	li %r6, 952
	bl {vg_p192_mul_mod_n}
	li %r4, 496
	li %r5, 472
	li %r6, 664
	bl {vg_p192_mul_mod_n}
	li %r4, 520
	li %r5, 496
	li %r6, 664
	bl {vg_p192_mul_mod_n}
	li %r4, 544
	li %r5, 520
	li %r6, 664
	bl {vg_p192_mul_mod_n}
	li %r4, 568
	li %r5, 544
	li %r6, 664
	bl {vg_p192_mul_mod_n}
	li %r4, 592
	li %r5, 568
	li %r6, 664
	bl {vg_p192_mul_mod_n}
	li %r4, 616
	li %r5, 592
	li %r6, 664
	bl {vg_p192_mul_mod_n}
	li %r4, 640
	li %r5, 616
	li %r6, 664
	bl {vg_p192_mul_mod_n}
	ld %r4, 640(%r3)
	std %r4, 760(%r3)
	ld %r4, 648(%r3)
	std %r4, 768(%r3)
	ld %r4, 656(%r3)
	std %r4, 776(%r3)
	li %r31, 4
20:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
21:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
22:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
23:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
24:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
25:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
26:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
27:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
28:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
29:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
210:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
211:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
212:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
213:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
214:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
215:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
216:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
217:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
218:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
219:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
220:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
221:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
222:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 4
223:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 760
	li %r5, 760
	li %r6, 568
	bl {vg_p192_mul_mod_n}
	li %r31, 4
224:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 760
	li %r5, 760
	li %r6, 568
	bl {vg_p192_mul_mod_n}
	li %r31, 4
225:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 760
	li %r5, 760
	li %r6, 616
	bl {vg_p192_mul_mod_n}
	li %r31, 3
226:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 760
	li %r5, 760
	li %r6, 544
	bl {vg_p192_mul_mod_n}
	li %r31, 5
227:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 1
228:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 760
	li %r5, 760
	li %r6, 472
	bl {vg_p192_mul_mod_n}
	li %r31, 9
229:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 760
	li %r5, 760
	li %r6, 616
	bl {vg_p192_mul_mod_n}
	li %r31, 1
230:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 760
	li %r5, 760
	li %r6, 472
	bl {vg_p192_mul_mod_n}
	li %r31, 7
231:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 760
	li %r5, 760
	li %r6, 520
	bl {vg_p192_mul_mod_n}
	li %r31, 7
232:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 760
	li %r5, 760
	li %r6, 616
	bl {vg_p192_mul_mod_n}
	li %r31, 5
233:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_n}
	li %r31, 6
234:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 760
	li %r5, 760
	li %r6, 568
	bl {vg_p192_mul_mod_n}
	li %r31, 4
235:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 760
	li %r5, 760
	li %r6, 592
	bl {vg_p192_mul_mod_n}
	li %r31, 7
236:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 760
	li %r5, 760
	li %r6, 616
	bl {vg_p192_mul_mod_n}
	li %r31, 3
237:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 760
	li %r5, 760
	li %r6, 520
	bl {vg_p192_mul_mod_n}
	li %r31, 6
238:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 760
	li %r5, 760
	li %r6, 616
	bl {vg_p192_mul_mod_n}
	li %r31, 3
239:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 760
	li %r5, 760
	li %r6, 472
	bl {vg_p192_mul_mod_n}
	li %r31, 6
240:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 760
	li %r5, 760
	li %r6, 520
	bl {vg_p192_mul_mod_n}
	li %r31, 9
241:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 760
	li %r5, 760
	li %r6, 592
	bl {vg_p192_mul_mod_n}
	li %r31, 2
242:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 760
	li %r5, 760
	li %r6, 496
	bl {vg_p192_mul_mod_n}
	ld %r0, 1152(%r3)
	mtlr %r0
	blr
