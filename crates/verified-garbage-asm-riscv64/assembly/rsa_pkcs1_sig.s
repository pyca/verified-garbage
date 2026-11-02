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
	ret
	.option pop
