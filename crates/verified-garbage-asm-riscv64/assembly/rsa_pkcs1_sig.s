// The functions of `src/rsa_pkcs1_sig.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_verify_precomputed:
	.option push
	.option arch, +m, +c
	addi t0, sp, 0
	ld t0, 0(t0)
	sub t0, t0, a1
	bnez t0, 20f
	addi sp, sp, -2032
	addi sp, sp, -96
	addi t0, sp, 0
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd ra, 48(t0)
	addi s1, a1, 0
	slli s2, a4, 32
	srli s2, s2, 32
	addi s3, a5, 0
	addi s4, a6, 0
	addi a4, a2, 0
	addi a5, a3, 0
	addi a6, a7, 0
	addi a7, a1, 0
	addi t6, sp, 2032
	addi t6, t6, 96
	ld t1, 8(t6)
	sd t1, 0(t0)
	ld t1, 16(t6)
	sd t1, 8(t0)
	ld a2, 24(t6)
	ld a3, 32(t6)
	addi a0, t0, 72
	addi a1, s1, 0
	call {vg_rsa_public_precomputed_checked}
	addi t0, sp, 0
	sd a0, 56(t0)
	addi a1, t0, 1096
	addi a2, s1, 0
	addi a3, s2, 0
	addi a4, s3, 0
	addi a5, s4, 0
	addi t3, a3, 0
	beqz t3, 22f
	addi t3, a3, -1
	beqz t3, 24f
	addi t3, a3, -2
	beqz t3, 26f
	addi t3, a3, -3
	beqz t3, 28f
	addi t3, a3, -4
	beqz t3, 210f
	addi t3, a3, -5
	beqz t3, 212f
	addi t3, a3, -6
	beqz t3, 214f
	addi t3, a3, -7
	beqz t3, 216f
	addi t3, a3, -8
	beqz t3, 218f
	addi t3, a3, -9
	beqz t3, 220f
	addi t3, a3, -10
	beqz t3, 222f
	addi t3, a3, -11
	beqz t3, 224f
	addi t3, zero, 2047
	addi t4, zero, 0
	j 225f
224:
	addi t3, zero, 83
	addi t4, zero, 64
225:
	j 223f
222:
	addi t3, zero, 67
	addi t4, zero, 48
223:
	j 221f
220:
	addi t3, zero, 51
	addi t4, zero, 32
221:
	j 219f
218:
	addi t3, zero, 47
	addi t4, zero, 28
219:
	j 217f
216:
	addi t3, zero, 51
	addi t4, zero, 32
217:
	j 215f
214:
	addi t3, zero, 47
	addi t4, zero, 28
215:
	j 213f
212:
	addi t3, zero, 83
	addi t4, zero, 64
213:
	j 211f
210:
	addi t3, zero, 67
	addi t4, zero, 48
211:
	j 29f
28:
	addi t3, zero, 51
	addi t4, zero, 32
29:
	j 27f
26:
	addi t3, zero, 47
	addi t4, zero, 28
27:
	j 25f
24:
	addi t3, zero, 35
	addi t4, zero, 20
25:
	j 23f
22:
	addi t3, zero, 34
	addi t4, zero, 16
23:
	sub t5, a5, t4
	bnez t5, 226f
	addi t5, t3, 11
	sub t5, a2, t5
	srli t5, t5, 63
	bnez t5, 228f
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	sub t5, a2, t3
	addi t5, t5, -3
	addi t0, zero, 255
230:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 230b
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t3, a3, 0
	beqz t3, 231f
	addi t3, a3, -1
	beqz t3, 233f
	addi t3, a3, -2
	beqz t3, 235f
	addi t3, a3, -3
	beqz t3, 237f
	addi t3, a3, -4
	beqz t3, 239f
	addi t3, a3, -5
	beqz t3, 241f
	addi t3, a3, -6
	beqz t3, 243f
	addi t3, a3, -7
	beqz t3, 245f
	addi t3, a3, -8
	beqz t3, 247f
	addi t3, a3, -9
	beqz t3, 249f
	addi t3, a3, -10
	beqz t3, 251f
	addi t3, a3, -11
	beqz t3, 253f
	j 254f
253:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 81
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 10
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 64
	sb t0, 0(a1)
	addi a1, a1, 1
254:
	j 252f
251:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 65
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
252:
	j 250f
249:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 8
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
250:
	j 248f
247:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 7
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
248:
	j 246f
245:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
246:
	j 244f
243:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
244:
	j 242f
241:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 81
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 64
	sb t0, 0(a1)
	addi a1, a1, 1
242:
	j 240f
239:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 65
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
240:
	j 238f
237:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
238:
	j 236f
235:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
236:
	j 234f
233:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 33
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 43
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 14
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 26
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 20
	sb t0, 0(a1)
	addi a1, a1, 1
234:
	j 232f
231:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 12
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 8
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 42
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 247
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 16
	sb t0, 0(a1)
	addi a1, a1, 1
232:
255:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 255b
	addi a0, zero, 1
	j 229f
228:
	addi a0, zero, 0
229:
	j 227f
226:
	addi a0, zero, 0
227:
	beqz a0, 256f
	addi t0, sp, 0
	addi a1, t0, 72
	addi a2, t0, 1096
	addi a3, s1, 0
	addi t4, zero, 0
258:
	lbu t0, 0(a1)
	lbu t1, 0(a2)
	xor t0, t0, t1
	or t4, t4, t0
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 258b
	addi a0, t4, -1
	srli a0, a0, 63
	j 257f
256:
	addi a0, zero, 0
257:
	addi t0, sp, 0
	ld a1, 56(t0)
	and a0, a0, a1
	addi t0, sp, 0
	ld s1, 16(t0)
	ld s2, 24(t0)
	ld s3, 32(t0)
	ld s4, 40(t0)
	ld ra, 48(t0)
	addi sp, sp, 96
	addi sp, sp, 2032
	j 21f
20:
	addi a0, zero, 0
21:
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -80
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	addi sp, sp, 80
	addi sp, sp, 16
	addi sp, sp, 2032
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_rsa_pkcs1_recover_precomputed:
	.option push
	.option arch, +m, +c
	addi t0, sp, 0
	ld t0, 0(t0)
	sub t0, t0, a3
	bnez t0, 20f
	addi sp, sp, -2032
	addi sp, sp, -96
	addi t0, sp, 0
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd ra, 48(t0)
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a3, 0
	slli s4, a6, 32
	srli s4, s4, 32
	addi a6, a7, 0
	addi a7, a3, 0
	addi t6, sp, 2032
	addi t6, t6, 96
	ld t1, 8(t6)
	sd t1, 0(t0)
	ld t1, 16(t6)
	sd t1, 8(t0)
	ld a2, 24(t6)
	ld a3, 32(t6)
	addi a0, t0, 72
	addi a1, s3, 0
	call {vg_rsa_public_precomputed_checked}
	addi t0, sp, 0
	sd a0, 56(t0)
	addi a1, t0, 1096
	addi a2, s3, 0
	addi a3, s4, 0
	addi a5, s2, 0
	addi a4, t0, 72
	add a4, a4, s3
	sub a4, a4, s2
	addi t3, a3, 0
	beqz t3, 22f
	addi t3, a3, -1
	beqz t3, 24f
	addi t3, a3, -2
	beqz t3, 26f
	addi t3, a3, -3
	beqz t3, 28f
	addi t3, a3, -4
	beqz t3, 210f
	addi t3, a3, -5
	beqz t3, 212f
	addi t3, a3, -6
	beqz t3, 214f
	addi t3, a3, -7
	beqz t3, 216f
	addi t3, a3, -8
	beqz t3, 218f
	addi t3, a3, -9
	beqz t3, 220f
	addi t3, a3, -10
	beqz t3, 222f
	addi t3, a3, -11
	beqz t3, 224f
	addi t3, zero, 2047
	addi t4, zero, 0
	j 225f
224:
	addi t3, zero, 83
	addi t4, zero, 64
225:
	j 223f
222:
	addi t3, zero, 67
	addi t4, zero, 48
223:
	j 221f
220:
	addi t3, zero, 51
	addi t4, zero, 32
221:
	j 219f
218:
	addi t3, zero, 47
	addi t4, zero, 28
219:
	j 217f
216:
	addi t3, zero, 51
	addi t4, zero, 32
217:
	j 215f
214:
	addi t3, zero, 47
	addi t4, zero, 28
215:
	j 213f
212:
	addi t3, zero, 83
	addi t4, zero, 64
213:
	j 211f
210:
	addi t3, zero, 67
	addi t4, zero, 48
211:
	j 29f
28:
	addi t3, zero, 51
	addi t4, zero, 32
29:
	j 27f
26:
	addi t3, zero, 47
	addi t4, zero, 28
27:
	j 25f
24:
	addi t3, zero, 35
	addi t4, zero, 20
25:
	j 23f
22:
	addi t3, zero, 34
	addi t4, zero, 16
23:
	sub t5, a5, t4
	bnez t5, 226f
	addi t5, t3, 11
	sub t5, a2, t5
	srli t5, t5, 63
	bnez t5, 228f
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	sub t5, a2, t3
	addi t5, t5, -3
	addi t0, zero, 255
230:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 230b
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t3, a3, 0
	beqz t3, 231f
	addi t3, a3, -1
	beqz t3, 233f
	addi t3, a3, -2
	beqz t3, 235f
	addi t3, a3, -3
	beqz t3, 237f
	addi t3, a3, -4
	beqz t3, 239f
	addi t3, a3, -5
	beqz t3, 241f
	addi t3, a3, -6
	beqz t3, 243f
	addi t3, a3, -7
	beqz t3, 245f
	addi t3, a3, -8
	beqz t3, 247f
	addi t3, a3, -9
	beqz t3, 249f
	addi t3, a3, -10
	beqz t3, 251f
	addi t3, a3, -11
	beqz t3, 253f
	j 254f
253:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 81
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 10
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 64
	sb t0, 0(a1)
	addi a1, a1, 1
254:
	j 252f
251:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 65
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
252:
	j 250f
249:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 8
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
250:
	j 248f
247:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 7
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
248:
	j 246f
245:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
246:
	j 244f
243:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
244:
	j 242f
241:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 81
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 64
	sb t0, 0(a1)
	addi a1, a1, 1
242:
	j 240f
239:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 65
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
240:
	j 238f
237:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
238:
	j 236f
235:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
236:
	j 234f
233:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 33
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 43
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 14
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 26
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 20
	sb t0, 0(a1)
	addi a1, a1, 1
234:
	j 232f
231:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 12
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 8
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 42
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 247
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 16
	sb t0, 0(a1)
	addi a1, a1, 1
232:
255:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 255b
	addi a0, zero, 1
	j 229f
228:
	addi a0, zero, 0
229:
	j 227f
226:
	addi a0, zero, 0
227:
	beqz a0, 256f
	addi t0, sp, 0
	addi a1, t0, 72
	addi a2, t0, 1096
	addi a3, s3, 0
	addi t4, zero, 0
258:
	lbu t0, 0(a1)
	lbu t1, 0(a2)
	xor t0, t0, t1
	or t4, t4, t0
	addi a1, a1, 1
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 258b
	addi a1, t4, -1
	srli a1, a1, 63
	addi t0, sp, 0
	ld a2, 56(t0)
	slli a2, a2, 32
	srli a2, a2, 32
	addi a3, zero, 0
	sub a2, a3, a2
	srli a2, a2, 63
	and a1, a1, a2
	sub a1, a3, a1
	sd a1, 64(t0)
	addi a1, s1, 0
	addi a5, s2, 0
	addi a4, t0, 72
	add a4, a4, s3
	sub a4, a4, s2
259:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 259b
	addi t0, sp, 0
	ld a3, 64(t0)
	addi a1, s1, 0
	addi a5, s2, 0
260:
	lbu t1, 0(a1)
	and t1, t1, a3
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 260b
	addi a0, zero, 1
	and a0, a0, a3
	j 257f
256:
	addi a1, s1, 0
	addi t5, s2, 0
	addi t0, zero, 0
261:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 261b
	addi a0, zero, 0
257:
	addi t0, sp, 0
	ld s1, 16(t0)
	ld s2, 24(t0)
	ld s3, 32(t0)
	ld s4, 40(t0)
	ld ra, 48(t0)
	addi sp, sp, 96
	addi sp, sp, 2032
	j 21f
20:
	addi t5, a1, 0
	addi a1, a0, 0
	addi t0, zero, 0
262:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 262b
	addi a0, zero, 0
21:
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -80
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	addi sp, sp, 80
	addi sp, sp, 16
	addi sp, sp, 2032
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_rsa_pkcs1_sign_precomputed:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1184
	addi t0, sp, 0
	sd s1, 112(t0)
	sd s2, 120(t0)
	sd s3, 128(t0)
	sd s4, 136(t0)
	sd s5, 144(t0)
	sd ra, 152(t0)
	addi s1, a0, 0
	addi s2, a2, 0
	addi s3, a3, 0
	addi s4, a4, 0
	addi s5, a5, 0
	addi t6, sp, 1184
	addi a1, t0, 160
	addi a2, s3, 0
	slli a3, a6, 32
	srli a3, a3, 32
	addi a4, a7, 0
	ld a5, 0(t6)
	addi t3, a3, 0
	beqz t3, 20f
	addi t3, a3, -1
	beqz t3, 22f
	addi t3, a3, -2
	beqz t3, 24f
	addi t3, a3, -3
	beqz t3, 26f
	addi t3, a3, -4
	beqz t3, 28f
	addi t3, a3, -5
	beqz t3, 210f
	addi t3, a3, -6
	beqz t3, 212f
	addi t3, a3, -7
	beqz t3, 214f
	addi t3, a3, -8
	beqz t3, 216f
	addi t3, a3, -9
	beqz t3, 218f
	addi t3, a3, -10
	beqz t3, 220f
	addi t3, a3, -11
	beqz t3, 222f
	addi t3, zero, 2047
	addi t4, zero, 0
	j 223f
222:
	addi t3, zero, 83
	addi t4, zero, 64
223:
	j 221f
220:
	addi t3, zero, 67
	addi t4, zero, 48
221:
	j 219f
218:
	addi t3, zero, 51
	addi t4, zero, 32
219:
	j 217f
216:
	addi t3, zero, 47
	addi t4, zero, 28
217:
	j 215f
214:
	addi t3, zero, 51
	addi t4, zero, 32
215:
	j 213f
212:
	addi t3, zero, 47
	addi t4, zero, 28
213:
	j 211f
210:
	addi t3, zero, 83
	addi t4, zero, 64
211:
	j 29f
28:
	addi t3, zero, 67
	addi t4, zero, 48
29:
	j 27f
26:
	addi t3, zero, 51
	addi t4, zero, 32
27:
	j 25f
24:
	addi t3, zero, 47
	addi t4, zero, 28
25:
	j 23f
22:
	addi t3, zero, 35
	addi t4, zero, 20
23:
	j 21f
20:
	addi t3, zero, 34
	addi t4, zero, 16
21:
	sub t5, a5, t4
	bnez t5, 224f
	addi t5, t3, 11
	sub t5, a2, t5
	srli t5, t5, 63
	bnez t5, 226f
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	sub t5, a2, t3
	addi t5, t5, -3
	addi t0, zero, 255
228:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 228b
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t3, a3, 0
	beqz t3, 229f
	addi t3, a3, -1
	beqz t3, 231f
	addi t3, a3, -2
	beqz t3, 233f
	addi t3, a3, -3
	beqz t3, 235f
	addi t3, a3, -4
	beqz t3, 237f
	addi t3, a3, -5
	beqz t3, 239f
	addi t3, a3, -6
	beqz t3, 241f
	addi t3, a3, -7
	beqz t3, 243f
	addi t3, a3, -8
	beqz t3, 245f
	addi t3, a3, -9
	beqz t3, 247f
	addi t3, a3, -10
	beqz t3, 249f
	addi t3, a3, -11
	beqz t3, 251f
	j 252f
251:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 81
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 10
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 64
	sb t0, 0(a1)
	addi a1, a1, 1
252:
	j 250f
249:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 65
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
250:
	j 248f
247:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 8
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
248:
	j 246f
245:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 7
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
246:
	j 244f
243:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
244:
	j 242f
241:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
242:
	j 240f
239:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 81
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 64
	sb t0, 0(a1)
	addi a1, a1, 1
240:
	j 238f
237:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 65
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
238:
	j 236f
235:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 49
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
236:
	j 234f
233:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 45
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 96
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 1
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 101
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 28
	sb t0, 0(a1)
	addi a1, a1, 1
234:
	j 232f
231:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 33
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 9
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 43
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 14
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 3
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 26
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 20
	sb t0, 0(a1)
	addi a1, a1, 1
232:
	j 230f
229:
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 32
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 48
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 12
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 6
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 8
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 42
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 72
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 134
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 247
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 13
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 2
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 0
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 4
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t0, zero, 16
	sb t0, 0(a1)
	addi a1, a1, 1
230:
253:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 253b
	addi a0, zero, 1
	j 227f
226:
	addi a0, zero, 0
227:
	j 225f
224:
	addi a0, zero, 0
225:
	beqz a0, 254f
	addi t0, sp, 0
	addi t6, sp, 1184
	ld t1, 8(t6)
	sd t1, 0(t0)
	ld t1, 16(t6)
	sd t1, 8(t0)
	ld t1, 24(t6)
	sd t1, 16(t0)
	ld t1, 32(t6)
	sd t1, 24(t0)
	ld t1, 40(t6)
	sd t1, 32(t0)
	ld t1, 48(t6)
	sd t1, 40(t0)
	ld t1, 56(t6)
	sd t1, 48(t0)
	ld t1, 64(t6)
	sd t1, 56(t0)
	ld t1, 72(t6)
	sd t1, 64(t0)
	ld t1, 80(t6)
	sd t1, 72(t0)
	ld t1, 88(t6)
	sd t1, 80(t0)
	ld t1, 96(t6)
	sd t1, 88(t0)
	ld t1, 104(t6)
	sd t1, 96(t0)
	ld t1, 112(t6)
	sd t1, 104(t0)
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, s2, 0
	addi a3, s3, 0
	addi a4, s4, 0
	addi a5, s5, 0
	addi a6, t0, 160
	addi a7, s3, 0
	call {vg_rsa_private_checked_precomputed}
	addi t0, sp, 0
	addi a1, t0, 160
	addi t5, s3, 0
	addi t0, zero, 0
256:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 256b
	j 255f
254:
	addi a1, s1, 0
	addi t5, s3, 0
	addi t0, zero, 0
257:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 257b
255:
	addi t0, sp, 0
	ld s1, 112(t0)
	ld s2, 120(t0)
	ld s3, 128(t0)
	ld s4, 136(t0)
	ld s5, 144(t0)
	ld ra, 152(t0)
	addi sp, sp, 1184
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -336
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	addi sp, sp, 336
	addi sp, sp, 16
	addi sp, sp, 2032
	addi sp, sp, 16
	addi sp, sp, 2032
	slli a0, a0, 32
	srli a0, a0, 32
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop
