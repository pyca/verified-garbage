// The functions of `src/internal/vg_brainpoolp512r1_inv_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_inv_mod_n:
	mflr %r0
	std %r0, 2952(%r3)
	ld %r4, 2432(%r3)
	std %r4, 1152(%r3)
	ld %r4, 2440(%r3)
	std %r4, 1160(%r3)
	ld %r4, 2448(%r3)
	std %r4, 1168(%r3)
	ld %r4, 2456(%r3)
	std %r4, 1176(%r3)
	ld %r4, 2464(%r3)
	std %r4, 1184(%r3)
	ld %r4, 2472(%r3)
	std %r4, 1192(%r3)
	ld %r4, 2480(%r3)
	std %r4, 1200(%r3)
	ld %r4, 2488(%r3)
	std %r4, 1208(%r3)
	li %r4, 1664
	li %r5, 2432
	li %r6, 2432
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1216
	li %r5, 1152
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1280
	li %r5, 1216
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1344
	li %r5, 1280
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1408
	li %r5, 1344
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1472
	li %r5, 1408
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1536
	li %r5, 1472
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1600
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	ld %r4, 1280(%r3)
	std %r4, 1920(%r3)
	ld %r4, 1288(%r3)
	std %r4, 1928(%r3)
	ld %r4, 1296(%r3)
	std %r4, 1936(%r3)
	ld %r4, 1304(%r3)
	std %r4, 1944(%r3)
	ld %r4, 1312(%r3)
	std %r4, 1952(%r3)
	ld %r4, 1320(%r3)
	std %r4, 1960(%r3)
	ld %r4, 1328(%r3)
	std %r4, 1968(%r3)
	ld %r4, 1336(%r3)
	std %r4, 1976(%r3)
	li %r31, 4
20:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
21:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
22:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
23:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
24:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
25:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 1
26:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
27:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
28:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
29:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
210:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 2
211:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
212:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
213:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
214:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
215:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
216:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
217:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
218:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
219:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 1
220:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
221:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
222:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
223:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
224:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 2
225:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 11
226:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
227:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
228:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
229:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
230:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
231:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
232:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
233:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
234:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
235:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
236:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
237:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
238:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
239:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
240:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
241:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
242:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
243:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
244:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
245:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
246:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
247:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
248:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
249:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
250:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
251:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
252:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
253:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
254:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
255:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
256:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
257:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
258:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
259:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
260:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
261:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
262:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 262b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 1
263:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 263b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
264:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 264b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
265:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
266:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
267:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
268:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
269:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
270:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 270b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
271:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
272:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 272b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
273:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 273b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
274:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 274b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
275:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 275b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
276:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 276b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
277:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 277b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
278:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
279:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 1
280:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 280b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
281:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 281b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
282:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 282b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 2
283:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 283b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
284:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 284b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
285:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 285b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
286:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 286b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
287:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 287b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
288:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 288b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
289:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 289b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
290:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 290b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
291:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 291b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
292:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 292b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
293:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 293b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
294:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 294b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
295:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 295b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 2
296:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 296b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
297:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 297b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
298:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 298b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
299:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 299b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2100:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2100b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 11
2101:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2101b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2102:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2102b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	ld %r0, 2952(%r3)
	mtlr %r0
	blr
