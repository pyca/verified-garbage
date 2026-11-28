// The functions of `src/internal/vg_p521_inv_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_inv_mod_n:
	mflr %r0
	std %r0, 3312(%r3)
	ld %r4, 2728(%r3)
	std %r4, 1288(%r3)
	ld %r4, 2736(%r3)
	std %r4, 1296(%r3)
	ld %r4, 2744(%r3)
	std %r4, 1304(%r3)
	ld %r4, 2752(%r3)
	std %r4, 1312(%r3)
	ld %r4, 2760(%r3)
	std %r4, 1320(%r3)
	ld %r4, 2768(%r3)
	std %r4, 1328(%r3)
	ld %r4, 2776(%r3)
	std %r4, 1336(%r3)
	ld %r4, 2784(%r3)
	std %r4, 1344(%r3)
	ld %r4, 2792(%r3)
	std %r4, 1352(%r3)
	li %r4, 1864
	li %r5, 2728
	li %r6, 2728
	bl {vg_p521_mul_mod_n}
	li %r4, 1360
	li %r5, 1288
	li %r6, 1864
	bl {vg_p521_mul_mod_n}
	li %r4, 1432
	li %r5, 1360
	li %r6, 1864
	bl {vg_p521_mul_mod_n}
	li %r4, 1504
	li %r5, 1432
	li %r6, 1864
	bl {vg_p521_mul_mod_n}
	li %r4, 1576
	li %r5, 1504
	li %r6, 1864
	bl {vg_p521_mul_mod_n}
	li %r4, 1648
	li %r5, 1576
	li %r6, 1864
	bl {vg_p521_mul_mod_n}
	li %r4, 1720
	li %r5, 1648
	li %r6, 1864
	bl {vg_p521_mul_mod_n}
	li %r4, 1792
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_mul_mod_n}
	ld %r4, 1792(%r3)
	std %r4, 2152(%r3)
	ld %r4, 1800(%r3)
	std %r4, 2160(%r3)
	ld %r4, 1808(%r3)
	std %r4, 2168(%r3)
	ld %r4, 1816(%r3)
	std %r4, 2176(%r3)
	ld %r4, 1824(%r3)
	std %r4, 2184(%r3)
	ld %r4, 1832(%r3)
	std %r4, 2192(%r3)
	ld %r4, 1840(%r3)
	std %r4, 2200(%r3)
	ld %r4, 1848(%r3)
	std %r4, 2208(%r3)
	ld %r4, 1856(%r3)
	std %r4, 2216(%r3)
	li %r31, 64
20:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r31, 4
21:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1720
	bl {vg_p521_mul_mod_n}
	li %r31, 5
22:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1432
	bl {vg_p521_mul_mod_n}
	li %r31, 5
23:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1360
	bl {vg_p521_mul_mod_n}
	li %r31, 8
24:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1720
	bl {vg_p521_mul_mod_n}
	li %r31, 8
25:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_n}
	li %r31, 8
26:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	li %r31, 5
27:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_n}
	li %r31, 2
28:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1360
	bl {vg_p521_mul_mod_n}
	li %r31, 6
29:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1648
	bl {vg_p521_mul_mod_n}
	li %r31, 3
210:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	li %r31, 6
211:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1648
	bl {vg_p521_mul_mod_n}
	li %r31, 6
212:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1720
	bl {vg_p521_mul_mod_n}
	li %r31, 5
213:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1720
	bl {vg_p521_mul_mod_n}
	li %r31, 4
214:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_n}
	li %r31, 4
215:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_n}
	li %r31, 4
216:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1360
	bl {vg_p521_mul_mod_n}
	li %r31, 12
217:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1432
	bl {vg_p521_mul_mod_n}
	li %r31, 3
218:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1288
	bl {vg_p521_mul_mod_n}
	li %r31, 7
219:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_n}
	li %r31, 4
220:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	li %r31, 8
221:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1576
	bl {vg_p521_mul_mod_n}
	li %r31, 3
222:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1432
	bl {vg_p521_mul_mod_n}
	li %r31, 6
223:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1648
	bl {vg_p521_mul_mod_n}
	li %r31, 3
224:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1432
	bl {vg_p521_mul_mod_n}
	li %r31, 9
225:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	li %r31, 4
226:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	li %r31, 5
227:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1720
	bl {vg_p521_mul_mod_n}
	li %r31, 4
228:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	li %r31, 6
229:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1576
	bl {vg_p521_mul_mod_n}
	li %r31, 4
230:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1648
	bl {vg_p521_mul_mod_n}
	li %r31, 1
231:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1288
	bl {vg_p521_mul_mod_n}
	li %r31, 4
232:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1288
	bl {vg_p521_mul_mod_n}
	li %r31, 7
233:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1576
	bl {vg_p521_mul_mod_n}
	li %r31, 4
234:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1576
	bl {vg_p521_mul_mod_n}
	li %r31, 2
235:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1360
	bl {vg_p521_mul_mod_n}
	li %r31, 4
236:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1288
	bl {vg_p521_mul_mod_n}
	li %r31, 7
237:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_n}
	li %r31, 5
238:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1648
	bl {vg_p521_mul_mod_n}
	li %r31, 3
239:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1432
	bl {vg_p521_mul_mod_n}
	li %r31, 4
240:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	li %r31, 5
241:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1720
	bl {vg_p521_mul_mod_n}
	li %r31, 4
242:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1648
	bl {vg_p521_mul_mod_n}
	li %r31, 3
243:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	li %r31, 5
244:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1720
	bl {vg_p521_mul_mod_n}
	li %r31, 2
245:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1360
	bl {vg_p521_mul_mod_n}
	li %r31, 7
246:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_n}
	li %r31, 5
247:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1576
	bl {vg_p521_mul_mod_n}
	li %r31, 7
248:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1576
	bl {vg_p521_mul_mod_n}
	li %r31, 2
249:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1360
	bl {vg_p521_mul_mod_n}
	li %r31, 6
250:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1360
	bl {vg_p521_mul_mod_n}
	li %r31, 3
251:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1288
	bl {vg_p521_mul_mod_n}
	li %r31, 10
252:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_n}
	ld %r0, 3312(%r3)
	mtlr %r0
	blr
