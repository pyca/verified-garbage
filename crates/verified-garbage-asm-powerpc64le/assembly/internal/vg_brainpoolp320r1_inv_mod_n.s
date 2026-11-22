// The functions of `src/internal/vg_brainpoolp320r1_inv_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_inv_mod_n:
	mflr %r0
	std %r0, 1872(%r3)
	ld %r4, 1544(%r3)
	std %r4, 744(%r3)
	ld %r4, 1552(%r3)
	std %r4, 752(%r3)
	ld %r4, 1560(%r3)
	std %r4, 760(%r3)
	ld %r4, 1568(%r3)
	std %r4, 768(%r3)
	ld %r4, 1576(%r3)
	std %r4, 776(%r3)
	li %r4, 1064
	li %r5, 1544
	li %r6, 1544
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 784
	li %r5, 744
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 824
	li %r5, 784
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 864
	li %r5, 824
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 904
	li %r5, 864
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 944
	li %r5, 904
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 984
	li %r5, 944
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1024
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	ld %r4, 984(%r3)
	std %r4, 1224(%r3)
	ld %r4, 992(%r3)
	std %r4, 1232(%r3)
	ld %r4, 1000(%r3)
	std %r4, 1240(%r3)
	ld %r4, 1008(%r3)
	std %r4, 1248(%r3)
	ld %r4, 1016(%r3)
	std %r4, 1256(%r3)
	li %r31, 6
20:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
21:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
22:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
23:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
24:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 11
25:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
26:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
27:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
28:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
29:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
210:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
211:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
212:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
213:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
214:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
215:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
216:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
217:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
218:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
219:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 12
220:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
221:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
222:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
223:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
224:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
225:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 2
226:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
227:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
228:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
229:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
230:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
231:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
232:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
233:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
234:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
235:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
236:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
237:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
238:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 9
239:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
240:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
241:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
242:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
243:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
244:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
245:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
246:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
247:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
248:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
249:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
250:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
251:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
252:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
253:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
254:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
255:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
256:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
257:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
258:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
259:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
260:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
261:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	ld %r0, 1872(%r3)
	mtlr %r0
	blr
