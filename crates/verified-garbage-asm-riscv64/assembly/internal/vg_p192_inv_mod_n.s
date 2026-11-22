// The functions of `src/internal/vg_p192_inv_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_inv_mod_n:
	.option push
	.option arch, +m, +c
	sd ra, 1504(s0)
	addi a0, s0, 0
	addi a1, zero, 1536
	addi a2, zero, 704
	addi a3, zero, 1216
	call {vg_p192_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1536
	addi a3, zero, 1536
	call {vg_p192_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1568
	addi a2, zero, 1536
	addi a3, zero, 1792
	call {vg_p192_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1600
	addi a2, zero, 1568
	addi a3, zero, 1792
	call {vg_p192_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1632
	addi a2, zero, 1600
	addi a3, zero, 1792
	call {vg_p192_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1664
	addi a2, zero, 1632
	addi a3, zero, 1792
	call {vg_p192_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1696
	addi a2, zero, 1664
	addi a3, zero, 1792
	call {vg_p192_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1728
	addi a2, zero, 1696
	addi a3, zero, 1792
	call {vg_p192_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 1760
	addi a2, zero, 1728
	addi a3, zero, 1792
	call {vg_p192_mul_mod_n}
	ld t0, 1760(s0)
	sd t0, 992(s0)
	ld t0, 1768(s0)
	sd t0, 1000(s0)
	ld t0, 1776(s0)
	sd t0, 1008(s0)
	ld t0, 1784(s0)
	sd t0, 1016(s0)
	addi s1, zero, 4
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_p192_mul_mod_n}
	addi s1, zero, 3
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1632
	call {vg_p192_mul_mod_n}
	addi s1, zero, 5
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 1
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p192_mul_mod_n}
	addi s1, zero, 9
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_p192_mul_mod_n}
	addi s1, zero, 1
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p192_mul_mod_n}
	addi s1, zero, 7
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_p192_mul_mod_n}
	addi s1, zero, 7
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_p192_mul_mod_n}
	addi s1, zero, 5
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1760
	call {vg_p192_mul_mod_n}
	addi s1, zero, 6
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1664
	call {vg_p192_mul_mod_n}
	addi s1, zero, 4
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_p192_mul_mod_n}
	addi s1, zero, 7
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_p192_mul_mod_n}
	addi s1, zero, 3
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_p192_mul_mod_n}
	addi s1, zero, 6
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1728
	call {vg_p192_mul_mod_n}
	addi s1, zero, 3
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1536
	call {vg_p192_mul_mod_n}
	addi s1, zero, 6
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1600
	call {vg_p192_mul_mod_n}
	addi s1, zero, 9
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1696
	call {vg_p192_mul_mod_n}
	addi s1, zero, 2
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_n}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 1568
	call {vg_p192_mul_mod_n}
	ld ra, 1504(s0)
	ret
	.option pop
