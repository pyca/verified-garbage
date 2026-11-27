// The functions of `src/internal/vg_p521_inv_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_inv_mod_p:
	mflr %r0
	std %r0, 3312(%r3)
	ld %r4, 1216(%r3)
	std %r4, 1288(%r3)
	ld %r4, 1224(%r3)
	std %r4, 1296(%r3)
	ld %r4, 1232(%r3)
	std %r4, 1304(%r3)
	ld %r4, 1240(%r3)
	std %r4, 1312(%r3)
	ld %r4, 1248(%r3)
	std %r4, 1320(%r3)
	ld %r4, 1256(%r3)
	std %r4, 1328(%r3)
	ld %r4, 1264(%r3)
	std %r4, 1336(%r3)
	ld %r4, 1272(%r3)
	std %r4, 1344(%r3)
	ld %r4, 1280(%r3)
	std %r4, 1352(%r3)
	li %r4, 1864
	li %r5, 1216
	li %r6, 1216
	bl {vg_p521_mul_mod_p}
	li %r4, 1360
	li %r5, 1288
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1360
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1504
	li %r5, 1432
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1576
	li %r5, 1504
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1648
	li %r5, 1576
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1720
	li %r5, 1648
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
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
	li %r31, 4
20:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
21:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
22:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
23:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
24:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
25:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
26:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
27:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
28:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
29:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
210:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
211:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
212:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
213:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
214:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
215:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
216:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
217:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
218:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
219:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
220:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
221:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
222:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
223:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
224:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
225:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
226:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
227:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
228:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
229:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
230:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
231:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
232:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
233:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
234:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
235:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
236:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
237:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
238:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
239:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
240:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
241:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
242:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
243:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
244:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
245:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
246:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
247:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
248:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
249:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
250:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
251:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
252:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
253:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
254:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
255:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
256:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
257:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
258:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
259:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
260:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
261:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
262:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 262b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
263:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 263b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
264:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 264b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
265:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
266:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
267:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
268:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
269:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
270:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 270b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
271:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
272:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 272b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
273:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 273b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
274:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 274b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
275:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 275b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
276:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 276b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
277:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 277b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
278:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
279:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
280:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 280b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
281:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 281b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
282:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 282b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
283:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 283b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
284:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 284b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
285:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 285b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
286:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 286b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
287:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 287b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
288:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 288b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
289:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 289b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
290:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 290b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
291:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 291b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
292:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 292b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
293:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 293b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
294:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 294b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
295:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 295b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
296:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 296b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
297:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 297b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
298:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 298b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
299:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 299b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2100:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2100b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2101:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2101b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2102:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2102b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2103:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2103b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2104:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2104b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2105:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2105b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2106:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2106b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2107:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2107b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2108:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2108b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2109:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2109b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2110:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2110b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2111:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2111b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2112:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2112b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2113:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2113b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2114:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2114b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2115:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2115b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2116:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2116b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2117:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2117b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2118:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2118b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2119:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2119b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2120:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2120b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2121:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2121b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2122:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2122b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2123:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2123b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2124:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2124b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2125:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2125b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2126:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2126b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 4
2127:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2127b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r31, 3
2128:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2128b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_p}
	li %r31, 2
2129:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2129b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	ld %r0, 3312(%r3)
	mtlr %r0
	blr
