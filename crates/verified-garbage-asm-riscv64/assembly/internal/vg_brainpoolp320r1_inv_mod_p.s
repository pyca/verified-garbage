// The functions of `src/internal/vg_brainpoolp320r1_inv_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_inv_mod_p:
	.option push
	.option arch, +m, +c
	sd ra, 1864(s0)
	addi a0, s0, 0
	addi a1, zero, 1904
	addi a2, zero, 704
	addi a3, zero, 264
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 177
	addi a2, zero, 1904
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1944
	addi a2, zero, 1904
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1984
	addi a2, zero, 1944
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2024
	addi a2, zero, 1984
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 17
	addi a2, zero, 2024
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 57
	addi a2, zero, 2047
	addi a2, a2, 17
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 97
	addi a2, zero, 2047
	addi a2, a2, 57
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 137
	addi a2, zero, 2047
	addi a2, a2, 97
	addi a3, zero, 2047
	addi a3, a3, 177
	call {vg_brainpoolp320r1_mul_mod_p}
	addi t0, s0, 2047
	ld t0, 97(t0)
	sd t0, 1224(s0)
	addi t0, s0, 2047
	ld t0, 105(t0)
	sd t0, 1232(s0)
	addi t0, s0, 2047
	ld t0, 113(t0)
	sd t0, 1240(s0)
	addi t0, s0, 2047
	ld t0, 121(t0)
	sd t0, 1248(s0)
	addi t0, s0, 2047
	ld t0, 129(t0)
	sd t0, 1256(s0)
	addi s1, zero, 6
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
21:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 21b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
22:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 22b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
23:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 23b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
24:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 24b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 11
25:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 25b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
26:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 26b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
27:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 27b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
28:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 28b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
29:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 29b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
210:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 210b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
211:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 211b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 1
212:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 212b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
213:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 213b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
214:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 214b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
215:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 215b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
216:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 216b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
217:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 217b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
218:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 218b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
219:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 219b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 12
220:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 220b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 8
221:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 221b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
222:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 222b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
223:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 223b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
224:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 224b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
225:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 225b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
226:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 226b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
227:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 227b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
228:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 228b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
229:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 229b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
230:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 230b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
231:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 231b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
232:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 232b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
233:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 233b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 10
234:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 234b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
235:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 235b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
236:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 236b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
237:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 237b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
238:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 238b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
239:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 239b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
240:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 240b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
241:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 241b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
242:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 242b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 3
243:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 243b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
244:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 244b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
245:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 245b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
246:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 246b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
247:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 247b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
248:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 248b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1984
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
249:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 249b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
250:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 250b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1944
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 6
251:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 251b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
252:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 252b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 9
253:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 253b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 5
254:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 254b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 57
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
255:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 255b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 137
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 1
256:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 256b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
257:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 257b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 97
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
258:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 258b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
259:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 259b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 4
260:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 260b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2024
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 7
261:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 261b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 2047
	addi a3, a3, 17
	call {vg_brainpoolp320r1_mul_mod_p}
	addi s1, zero, 2
262:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1224
	call {vg_brainpoolp320r1_mul_mod_p}
	bnez s1, 262b
	addi a0, s0, 0
	addi a1, zero, 1224
	addi a2, zero, 1224
	addi a3, zero, 1904
	call {vg_brainpoolp320r1_mul_mod_p}
	ld ra, 1864(s0)
	ret
	.option pop
