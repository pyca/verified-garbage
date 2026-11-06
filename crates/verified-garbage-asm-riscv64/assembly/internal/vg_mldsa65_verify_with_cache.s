// The functions of `src/internal/vg_mldsa65_verify_with_cache.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_verify_with_cache:
	.option push
	.option arch, +m, +c
	sd s3, 1288(a3)
	sd s4, 1296(a3)
	sd s5, 1304(a3)
	sd s6, 1312(a3)
	sd s7, 1320(a3)
	sd s8, 1328(a3)
	sd s9, 1336(a3)
	sd s10, 1344(a3)
	sd s11, 1352(a3)
	sd ra, 1360(a3)
	addi s10, a0, 0
	addi s9, a1, 0
	addi s8, a2, 0
	addi s11, a3, 0
	addi s4, zero, 1
	addi t2, zero, 0
	sltu t0, t2, a5
	sub t0, t2, t0
	and s3, a4, t0
	lui a0, 1
	addi a0, a0, -848
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 61
	lui a2, 0
	addi a2, a2, 55
	lui a3, 2
	addi a3, a3, 0
	add a3, s11, a3
	lui a4, 0
	addi a4, a4, 1536
	call {vg_mldsa_hint_bit_unpack}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 20f
	j 21f
20:
	lui a0, 0
	addi a0, a0, 48
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 640
	lui a2, 128
	addi a2, a2, -1
	lui a3, 128
	addi a3, a3, 0
	lui a4, 4
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -196
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 0
	addi a0, a0, 688
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 640
	lui a2, 128
	addi a2, a2, -1
	lui a3, 128
	addi a3, a3, 0
	lui a4, 4
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -196
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 0
	addi a0, a0, 1328
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 640
	lui a2, 128
	addi a2, a2, -1
	lui a3, 128
	addi a3, a3, 0
	lui a4, 5
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -196
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 0
	addi a0, a0, 1968
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 640
	lui a2, 128
	addi a2, a2, -1
	lui a3, 128
	addi a3, a3, 0
	lui a4, 5
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -196
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 1
	addi a0, a0, -1488
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 640
	lui a2, 128
	addi a2, a2, -1
	lui a3, 128
	addi a3, a3, 0
	lui a4, 5
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -196
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 22f
	j 23f
22:
	addi a0, s10, 0
	addi a1, s11, 920
	addi a2, zero, 32
24:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 24b
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 7
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
25:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 25b
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
26:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 26b
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 8
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
27:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 27b
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 8
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
28:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 28b
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 8
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
29:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 29b
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 9
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
210:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 210b
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 9
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
211:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 211b
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
212:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 212b
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
213:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 213b
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
214:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 214b
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
215:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 215b
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
216:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 216b
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 12
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
217:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 217b
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 12
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
218:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 218b
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 12
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
219:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 219b
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 13
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
220:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 220b
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 13
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
221:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 221b
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 14
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
222:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 222b
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 14
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
223:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 223b
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 14
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
224:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 224b
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 15
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 15
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
225:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 225b
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 15
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 15
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
226:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 226b
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 16
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
227:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 227b
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 16
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
228:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 228b
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 16
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
229:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 229b
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 17
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
230:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 230b
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 17
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
231:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 231b
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 18
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
232:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 232b
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 18
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
233:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 233b
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 18
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
234:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 234b
	lui a0, 0
	addi a0, a0, 0
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 48
	lui a2, 0
	addi a2, a2, 49
	lui a3, 6
	addi a3, a3, -1024
	add a3, s11, a3
	lui a4, 1
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_sample_in_ball}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
235:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 235b
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	bnez s3, 236f
	lui a0, 0
	addi a0, a0, 32
	add a0, s10, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	j 237f
236:
	lui a0, 0
	addi a0, a0, 0
	add a0, s3, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 0
	addi a2, a2, 1024
238:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 238b
237:
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	bnez s3, 239f
	lui a0, 0
	addi a0, a0, 352
	add a0, s10, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	j 240f
239:
	lui a0, 0
	addi a0, a0, 1024
	add a0, s3, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 0
	addi a2, a2, 1024
241:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 241b
240:
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1920
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	bnez s3, 242f
	lui a0, 0
	addi a0, a0, 672
	add a0, s10, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	j 243f
242:
	lui a0, 1
	addi a0, a0, -2048
	add a0, s3, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 0
	addi a2, a2, 1024
244:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 244b
243:
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 3
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1792
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	bnez s3, 245f
	lui a0, 0
	addi a0, a0, 992
	add a0, s10, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	j 246f
245:
	lui a0, 1
	addi a0, a0, -1024
	add a0, s3, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 0
	addi a2, a2, 1024
247:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 247b
246:
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 3
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1664
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 15
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 15
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	bnez s3, 248f
	lui a0, 0
	addi a0, a0, 1312
	add a0, s10, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	j 249f
248:
	lui a0, 1
	addi a0, a0, 0
	add a0, s3, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 0
	addi a2, a2, 1024
250:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 250b
249:
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 3
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1536
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 4
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	bnez s3, 251f
	lui a0, 0
	addi a0, a0, 1632
	add a0, s10, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_ntt}
	j 252f
251:
	lui a0, 1
	addi a0, a0, 1024
	add a0, s3, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 0
	addi a2, a2, 1024
253:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 253b
252:
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 3
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1408
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s9, 0
	addi a4, zero, 64
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	addi a4, zero, 768
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	addi a4, zero, 48
	call {vg_keccak_squeeze}
	lui a0, 1
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	lui s6, 0
	addi s6, s6, 48
	addi t2, zero, 0
254:
	lbu a2, 0(a0)
	lbu a3, 0(a1)
	xor a2, a2, a3
	or t2, t2, a2
	addi a0, a0, 1
	addi a1, a1, 1
	addi s6, s6, -1
	bnez s6, 254b
	addi t2, t2, -1
	srli t2, t2, 63
	and s4, s4, t2
23:
21:
	addi a0, s4, 0
	ld ra, 1360(s11)
	ld s3, 1288(s11)
	ld s4, 1296(s11)
	ld s5, 1304(s11)
	ld s6, 1312(s11)
	ld s7, 1320(s11)
	ld s8, 1328(s11)
	ld s9, 1336(s11)
	ld s10, 1344(s11)
	ld s11, 1352(s11)
	ret
	.option pop
