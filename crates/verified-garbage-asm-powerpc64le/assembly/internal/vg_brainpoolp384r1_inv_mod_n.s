// The functions of `src/internal/vg_brainpoolp384r1_inv_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp384r1_inv_mod_n:
	mflr %r0
	std %r0, 2232(%r3)
	ld %r4, 1840(%r3)
	std %r4, 880(%r3)
	ld %r4, 1848(%r3)
	std %r4, 888(%r3)
	ld %r4, 1856(%r3)
	std %r4, 896(%r3)
	ld %r4, 1864(%r3)
	std %r4, 904(%r3)
	ld %r4, 1872(%r3)
	std %r4, 912(%r3)
	ld %r4, 1880(%r3)
	std %r4, 920(%r3)
	li %r4, 1264
	li %r5, 1840
	li %r6, 1840
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 928
	li %r5, 880
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 976
	li %r5, 928
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1024
	li %r5, 976
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1120
	li %r5, 1072
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1168
	li %r5, 1120
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_n}
	ld %r4, 880(%r3)
	std %r4, 1456(%r3)
	ld %r4, 888(%r3)
	std %r4, 1464(%r3)
	ld %r4, 896(%r3)
	std %r4, 1472(%r3)
	ld %r4, 904(%r3)
	std %r4, 1480(%r3)
	ld %r4, 912(%r3)
	std %r4, 1488(%r3)
	ld %r4, 920(%r3)
	std %r4, 1496(%r3)
	li %r31, 5
20:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 6
21:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
22:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 7
23:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 2
24:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 8
25:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 2
26:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
27:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
28:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 8
29:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
210:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
211:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 11
212:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
213:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
214:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
215:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
216:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
217:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 2
218:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
219:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 7
220:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
221:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
222:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 8
223:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
224:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 1
225:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 6
226:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
227:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
228:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
229:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
230:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 8
231:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
232:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
233:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
234:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 2
235:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 6
236:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
237:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
238:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
239:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 7
240:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 1
241:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 7
242:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 6
243:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 2
244:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 6
245:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
246:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
247:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 8
248:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 8
249:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
250:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 6
251:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
252:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
253:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
254:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
255:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
256:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
257:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
258:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
259:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
260:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
261:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
262:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 262b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
263:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 263b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 6
264:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 264b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
265:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 9
266:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
267:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 4
268:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 7
269:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
270:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 270b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 11
271:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
272:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 272b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
273:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 273b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 6
274:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 274b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
275:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 275b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
276:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 276b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 3
277:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 277b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 5
278:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_n}
	ld %r0, 2232(%r3)
	mtlr %r0
	blr
