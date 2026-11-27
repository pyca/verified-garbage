// The functions of `src/internal/vg_brainpoolp512r1_inv_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_inv_mod_p:
	.option push
	.option arch, +m, +c
	addi s0, s0, 2047
	sd ra, 897(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 961
	addi a2, zero, 1088
	addi a3, zero, 384
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1473
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1025
	addi a2, zero, 2047
	addi a2, a2, 961
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1089
	addi a2, zero, 2047
	addi a2, a2, 1025
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1153
	addi a2, zero, 2047
	addi a2, a2, 1089
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1217
	addi a2, zero, 2047
	addi a2, a2, 1153
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1281
	addi a2, zero, 2047
	addi a2, a2, 1217
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1345
	addi a2, zero, 2047
	addi a2, a2, 1281
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1409
	addi a2, zero, 2047
	addi a2, a2, 1345
	addi a3, zero, 2047
	addi a3, a3, 1473
	call {vg_brainpoolp512r1_mul_mod_p}
	addi t0, s0, 2047
	ld t0, 1089(t0)
	sd t0, 1920(s0)
	addi t0, s0, 2047
	ld t0, 1097(t0)
	sd t0, 1928(s0)
	addi t0, s0, 2047
	ld t0, 1105(t0)
	sd t0, 1936(s0)
	addi t0, s0, 2047
	ld t0, 1113(t0)
	sd t0, 1944(s0)
	addi t0, s0, 2047
	ld t0, 1121(t0)
	sd t0, 1952(s0)
	addi t0, s0, 2047
	ld t0, 1129(t0)
	sd t0, 1960(s0)
	addi t0, s0, 2047
	ld t0, 1137(t0)
	sd t0, 1968(s0)
	addi t0, s0, 2047
	ld t0, 1145(t0)
	sd t0, 1976(s0)
	addi s1, zero, 4
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 1
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 2
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 1
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 2
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 11
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 8
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 8
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 12
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 2
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
263:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 263b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
264:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 264b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
265:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 265b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
266:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 266b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
267:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 267b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
268:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 268b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 8
269:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 269b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
270:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 270b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
271:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 271b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
272:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 272b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 2
273:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 273b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
274:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 274b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 10
275:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 275b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
276:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 276b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
277:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 277b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
278:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 278b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 10
279:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 279b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
280:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 280b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
281:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 281b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
282:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 282b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
283:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 283b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
284:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 284b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 9
285:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 285b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
286:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 286b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1345
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
287:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 287b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
288:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 288b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
289:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 289b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
290:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 290b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
291:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 291b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 9
292:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 292b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1089
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
293:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 293b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1025
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 6
294:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 294b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1281
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 8
295:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 295b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1153
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 5
296:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 296b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1217
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 3
297:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 297b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 7
298:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 298b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 1409
	call {vg_brainpoolp512r1_mul_mod_p}
	addi s1, zero, 4
299:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 1920
	call {vg_brainpoolp512r1_mul_mod_p}
	bnez s1, 299b
	addi a0, s0, 0
	addi a1, zero, 1920
	addi a2, zero, 1920
	addi a3, zero, 2047
	addi a3, a3, 961
	call {vg_brainpoolp512r1_mul_mod_p}
	addi ra, s0, 2047
	ld ra, 897(ra)
	ret
	.option pop
