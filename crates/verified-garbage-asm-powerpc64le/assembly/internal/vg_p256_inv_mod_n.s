// The functions of `src/internal/vg_p256_inv_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_inv_mod_n:
	mflr %r0
	std %r0, 1512(%r3)
	ld %r4, 1248(%r3)
	std %r4, 608(%r3)
	ld %r4, 1256(%r3)
	std %r4, 616(%r3)
	ld %r4, 1264(%r3)
	std %r4, 624(%r3)
	ld %r4, 1272(%r3)
	std %r4, 632(%r3)
	li %r4, 864
	li %r5, 1248
	li %r6, 1248
	bl {vg_p256_mul_mod_n}
	li %r4, 640
	li %r5, 608
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 672
	li %r5, 640
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 704
	li %r5, 672
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 736
	li %r5, 704
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 768
	li %r5, 736
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 800
	li %r5, 768
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 832
	li %r5, 800
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	ld %r4, 832(%r3)
	std %r4, 992(%r3)
	ld %r4, 840(%r3)
	std %r4, 1000(%r3)
	ld %r4, 848(%r3)
	std %r4, 1008(%r3)
	ld %r4, 856(%r3)
	std %r4, 1016(%r3)
	li %r31, 7
20:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r31, 36
21:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 15
22:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r31, 4
23:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p256_mul_mod_n}
	li %r31, 2
24:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 5
25:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 6
26:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 992
	li %r5, 992
	li %r6, 800
	bl {vg_p256_mul_mod_n}
	li %r31, 4
27:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
28:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p256_mul_mod_n}
	li %r31, 5
29:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p256_mul_mod_n}
	li %r31, 5
210:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 992
	li %r5, 992
	li %r6, 800
	bl {vg_p256_mul_mod_n}
	li %r31, 5
211:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 7
212:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p256_mul_mod_n}
	li %r31, 2
213:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 6
214:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 2
215:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p256_mul_mod_n}
	li %r31, 8
216:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 992
	li %r5, 992
	li %r6, 736
	bl {vg_p256_mul_mod_n}
	li %r31, 3
217:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 5
218:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 4
219:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 5
220:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 5
221:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p256_mul_mod_n}
	li %r31, 3
222:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 8
223:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p256_mul_mod_n}
	li %r31, 4
224:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 5
225:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 5
226:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 6
227:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 992
	li %r5, 992
	li %r6, 736
	bl {vg_p256_mul_mod_n}
	li %r31, 4
228:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p256_mul_mod_n}
	li %r31, 6
229:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	ld %r0, 1512(%r3)
	mtlr %r0
	blr
