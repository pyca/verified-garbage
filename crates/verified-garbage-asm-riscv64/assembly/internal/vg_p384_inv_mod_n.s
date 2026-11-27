// The functions of `src/internal/vg_p384_inv_mod_n.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_inv_mod_n:
	.option push
	.option arch, +m, +c
	addi s0, s0, 2047
	sd ra, 177(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 225
	addi a2, zero, 1024
	addi a3, zero, 1792
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 609
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 273
	addi a2, zero, 2047
	addi a2, a2, 225
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 321
	addi a2, zero, 2047
	addi a2, a2, 273
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 369
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 417
	addi a2, zero, 2047
	addi a2, a2, 369
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 417
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 513
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 561
	addi a2, zero, 2047
	addi a2, a2, 513
	addi a3, zero, 2047
	addi a3, a3, 609
	call {vg_p384_mul_mod_n}
	addi t0, s0, 2047
	ld t0, 561(t0)
	sd t0, 1456(s0)
	addi t0, s0, 2047
	ld t0, 569(t0)
	sd t0, 1464(s0)
	addi t0, s0, 2047
	ld t0, 577(t0)
	sd t0, 1472(s0)
	addi t0, s0, 2047
	ld t0, 585(t0)
	sd t0, 1480(s0)
	addi t0, s0, 2047
	ld t0, 593(t0)
	sd t0, 1488(s0)
	addi t0, s0, 2047
	ld t0, 601(t0)
	sd t0, 1496(s0)
	addi s1, zero, 4
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 2
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 7
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 1
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi s1, zero, 10
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 8
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 2
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 10
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 9
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 417
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi s1, zero, 7
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 7
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 561
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 369
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 7
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 3
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 273
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 5
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 321
	call {vg_p384_mul_mod_n}
	addi s1, zero, 6
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p384_mul_mod_n}
	addi s1, zero, 1
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi s1, zero, 4
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 1456
	call {vg_p384_mul_mod_n}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 1456
	addi a3, zero, 2047
	addi a3, a3, 225
	call {vg_p384_mul_mod_n}
	addi ra, s0, 2047
	ld ra, 177(ra)
	ret
	.option pop
