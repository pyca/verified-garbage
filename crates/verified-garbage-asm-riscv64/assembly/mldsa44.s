// The functions of `src/mldsa44.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_keygen:
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
	addi t0, zero, 4
	sb t0, 920(s11)
	addi t0, zero, 4
	sb t0, 921(s11)
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
	addi a3, s10, 0
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 920
	addi a4, zero, 2
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 1024
	addi a4, zero, 128
	call {vg_keccak_squeeze}
	addi a0, s11, 1024
	addi a1, s11, 1152
	addi a2, zero, 32
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	addi a0, s11, 1056
	addi a1, s11, 1216
	addi a2, zero, 64
21:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 21b
	addi t0, zero, 0
	sb t0, 1281(s11)
	addi t0, zero, 0
	sb t0, 1184(s11)
	addi t0, zero, 0
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
22:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 22b
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 0
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
23:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 23b
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 0
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
24:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 24b
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 0
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 2
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
25:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 25b
	addi t0, zero, 0
	sb t0, 1184(s11)
	addi t0, zero, 1
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
26:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 26b
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 1
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
27:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 27b
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 1
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 3
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
28:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 28b
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 1
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 3
	addi a1, a1, -1024
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
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 3
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
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 3
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
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 4
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
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 4
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
	addi t0, zero, 0
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 4
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
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 4
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
215:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 215b
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 5
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
216:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 216b
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 5
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
217:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 217b
	addi t0, zero, 0
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_rej_bounded_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 5
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
218:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 218b
	addi t0, zero, 1
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_rej_bounded_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 5
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
219:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 219b
	addi t0, zero, 2
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 6
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_rej_bounded_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 6
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
220:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 220b
	addi t0, zero, 3
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 6
	addi a2, a2, -1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_rej_bounded_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
221:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 221b
	addi t0, zero, 4
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 6
	addi a2, a2, 0
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_rej_bounded_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
222:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 222b
	addi t0, zero, 5
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_rej_bounded_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
223:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 223b
	addi t0, zero, 6
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_rej_bounded_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
224:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 224b
	addi t0, zero, 7
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_rej_bounded_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t2, zero, 0
	sub t2, t2, a0
	lui a1, 7
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
225:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 225b
	addi a0, s11, 1024
	addi a1, s9, 0
	addi a2, zero, 32
226:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 226b
	addi a0, s11, 1024
	addi a1, s8, 0
	addi a2, zero, 32
227:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 227b
	addi a0, s11, 1120
	addi a1, s8, 32
	addi a2, zero, 32
228:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 228b
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 128
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 5
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 224
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 320
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 416
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 512
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 608
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 704
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 800
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 5
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 7
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 32
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 8
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 896
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 7
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 352
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 8
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1312
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 7
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 672
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 8
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1728
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 7
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 992
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 8
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -1952
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
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
	addi a4, zero, 1024
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s9, 1024
	addi a4, zero, 288
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s8, 64
	addi a4, zero, 64
	call {vg_keccak_squeeze}
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

vg_mldsa44_sign:
	.option push
	.option arch, +m, +c
	sd s3, 1288(a4)
	sd s4, 1296(a4)
	sd s5, 1304(a4)
	sd s6, 1312(a4)
	sd s7, 1320(a4)
	sd s8, 1328(a4)
	sd s9, 1336(a4)
	sd s10, 1344(a4)
	sd s11, 1352(a4)
	sd ra, 1360(a4)
	addi s10, a0, 0
	addi s9, a1, 0
	addi s8, a2, 0
	addi s11, a4, 0
	sd a3, 912(s11)
	addi s4, zero, 1
	addi a0, s10, 0
	addi a1, s11, 920
	addi a2, zero, 32
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 2
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 0
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
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 1
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
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 2
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
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 3
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 0
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 1
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 2
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
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 3
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
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 21f
	j 22f
21:
	addi a0, s8, 0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 32
23:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 23b
	addi a0, s9, 0
	lui a1, 1
	addi a1, a1, -2016
	add a1, s11, a1
	addi a2, zero, 64
24:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 24b
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
	addi a3, s10, 32
	addi a4, zero, 32
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	lui a3, 1
	addi a3, a3, -2048
	add a3, s11, a3
	addi a4, zero, 96
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s11, 960
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	ld s8, 912(s11)
	lui a0, 0
	addi a0, a0, 128
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 7
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 7
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 224
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 7
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 320
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 7
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 416
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 7
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 7
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 512
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 8
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 8
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 608
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 8
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 8
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 704
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 8
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 800
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 8
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 896
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 9
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1312
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 9
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1728
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 9
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 1
	addi a0, a0, -1952
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 9
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi s7, zero, 0
	addi s5, zero, 814
25:
	addi a0, s7, 0
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, 0
	lui a2, 4
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 4
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 1024
26:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 26b
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 1
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, 0
	lui a2, 4
	addi a2, a2, -1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 4
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 1024
27:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 27b
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 2
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, 0
	lui a2, 4
	addi a2, a2, 0
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 1024
28:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 3
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, 0
	lui a2, 4
	addi a2, a2, 1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
29:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 29b
	lui a0, 5
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
	call {vg_mldsa_simple_bit_pack}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1856
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
	call {vg_mldsa_simple_bit_pack}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1664
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
	call {vg_mldsa_simple_bit_pack}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1472
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
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
	addi a3, s11, 1040
	addi a4, zero, 32
	call {vg_keccak_squeeze}
	lui a0, 0
	addi a0, a0, 1040
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 32
	lui a2, 0
	addi a2, a2, 39
	lui a3, 1
	addi a3, a3, 1024
	add a3, s11, a3
	lui a4, 1
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_sample_in_ball}
	slli a0, a0, 32
	srli a0, a0, 32
	bnez a0, 210f
	addi s4, zero, 0
	addi s5, zero, 1
	j 211f
210:
	lui a0, 1
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi s4, zero, 1
	addi s6, zero, 0
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 4
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 4
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 212f
	j 213f
212:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 4
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 4
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 214f
	j 215f
214:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 216f
	j 217f
216:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 218f
	j 219f
218:
219:
217:
215:
213:
	bnez s4, 220f
	j 221f
220:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 946
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 222f
	j 223f
222:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 946
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 224f
	j 225f
224:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 946
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 226f
	j 227f
226:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 946
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 228f
	j 229f
228:
229:
227:
225:
223:
	bnez s4, 230f
	j 231f
230:
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 9
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
232:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 232b
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 3
	addi a3, a3, -2048
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 9
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
233:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 233b
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 3
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 9
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
234:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 234b
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 3
	addi a3, a3, 0
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 9
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
235:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 235b
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 6
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 3
	addi a3, a3, 1024
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	addi a0, s6, -81
	srli a0, a0, 63
	and s4, s4, a0
231:
221:
	bnez s4, 236f
	addi s7, s7, 4
	j 237f
236:
	addi s5, zero, 1
237:
211:
	addi s5, s5, -1
	bnez s5, 25b
	bnez s4, 238f
	j 239f
238:
	addi a0, s11, 1040
	addi a1, s8, 0
	addi a2, zero, 32
240:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 240b
	lui a0, 4
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -1
	lui a2, 32
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 32
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 576
	call {vg_mldsa_bit_pack}
	lui a0, 4
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -1
	lui a2, 32
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 608
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 576
	call {vg_mldsa_bit_pack}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -1
	lui a2, 32
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1184
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 576
	call {vg_mldsa_bit_pack}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -1
	lui a2, 32
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1760
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 576
	call {vg_mldsa_bit_pack}
	lui a0, 3
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1024
	lui a2, 0
	addi a2, a2, 80
	lui a3, 1
	addi a3, a3, -1760
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 84
	call {vg_mldsa_hint_bit_pack}
239:
22:
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

vg_mldsa44_sign_message:
	.option push
	.option arch, +m, +c
	srli t1, a4, 8
	beqz t1, 20f
	addi a0, zero, 2
	j 21f
20:
	lui t2, 19
	addi t2, t2, 0
	add t2, a7, t2
	sd s0, 904(t2)
	sd s1, 912(t2)
	sd s2, 920(t2)
	sd s3, 928(t2)
	sd s4, 936(t2)
	sd s5, 944(t2)
	sd s6, 952(t2)
	sd s7, 960(t2)
	sd s8, 968(t2)
	sd ra, 976(t2)
	addi s0, a0, 0
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, a3, 0
	addi s4, a4, 0
	addi s5, a5, 0
	addi s6, a6, 0
	addi s7, a7, 0
	addi s8, t2, 0
	addi t0, zero, 0
	sb t0, 984(s8)
	sb s4, 985(s8)
	addi t0, zero, 0
	sd t0, 0(s8)
	sd t0, 8(s8)
	sd t0, 16(s8)
	sd t0, 24(s8)
	sd t0, 32(s8)
	sd t0, 40(s8)
	sd t0, 48(s8)
	sd t0, 56(s8)
	sd t0, 64(s8)
	sd t0, 72(s8)
	sd t0, 80(s8)
	sd t0, 88(s8)
	sd t0, 96(s8)
	sd t0, 104(s8)
	sd t0, 112(s8)
	sd t0, 120(s8)
	sd t0, 128(s8)
	sd t0, 136(s8)
	sd t0, 144(s8)
	sd t0, 152(s8)
	sd t0, 160(s8)
	sd t0, 168(s8)
	sd t0, 176(s8)
	sd t0, 184(s8)
	sd t0, 192(s8)
	addi a3, s0, 64
	addi a2, zero, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a4, zero, 64
	call {vg_keccak_absorb}
	addi a3, s8, 984
	addi a2, a0, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a4, zero, 2
	call {vg_keccak_absorb}
	addi a3, s3, 0
	addi a2, a0, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a4, s4, 0
	call {vg_keccak_absorb}
	addi a3, s1, 0
	addi a2, a0, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a4, s2, 0
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s8, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s8, 840
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	addi a0, s0, 0
	addi a1, s8, 840
	addi a2, s5, 0
	addi a3, s6, 0
	addi a4, s7, 0
	call {vg_mldsa44_sign}
	ld ra, 976(s8)
	ld s0, 904(s8)
	ld s1, 912(s8)
	ld s2, 920(s8)
	ld s3, 928(s8)
	ld s4, 936(s8)
	ld s5, 944(s8)
	ld s6, 952(s8)
	ld s7, 960(s8)
	ld s8, 968(s8)
21:
	ret
	.option pop

vg_mldsa44_verify:
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
	lui a0, 1
	addi a0, a0, -1760
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 84
	lui a2, 0
	addi a2, a2, 80
	lui a3, 2
	addi a3, a3, 0
	add a3, s11, a3
	lui a4, 0
	addi a4, a4, 1024
	call {vg_mldsa_hint_bit_unpack}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 20f
	j 21f
20:
	lui a0, 0
	addi a0, a0, 32
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 576
	lui a2, 32
	addi a2, a2, -1
	lui a3, 32
	addi a3, a3, 0
	lui a4, 4
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 4
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 0
	addi a0, a0, 608
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 576
	lui a2, 32
	addi a2, a2, -1
	lui a3, 32
	addi a3, a3, 0
	lui a4, 4
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 4
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 0
	addi a0, a0, 1184
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 576
	lui a2, 32
	addi a2, a2, -1
	lui a3, 32
	addi a3, a3, 0
	lui a4, 5
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	lui a0, 0
	addi a0, a0, 1760
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 576
	lui a2, 32
	addi a2, a2, -1
	lui a3, 32
	addi a3, a3, 0
	lui a4, 5
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 32
	addi a1, a1, -78
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
29:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 29b
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
210:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 210b
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
211:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 211b
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
212:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 212b
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
213:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 213b
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
214:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 214b
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
215:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 215b
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
216:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 216b
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
217:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 217b
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
218:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 218b
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
219:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 219b
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
220:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 220b
	lui a0, 0
	addi a0, a0, 0
	add a0, s8, a0
	lui a1, 0
	addi a1, a1, 32
	lui a2, 0
	addi a2, a2, 39
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
221:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 221b
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
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
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
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1856
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
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
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1664
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
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
	lui a2, 23
	addi a2, a2, 1024
	lui a3, 7
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_use_hint}
	lui a0, 7
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 43
	lui a2, 1
	addi a2, a2, -1472
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 192
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
	addi a4, zero, 32
	call {vg_keccak_squeeze}
	lui a0, 1
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	lui s6, 0
	addi s6, s6, 32
	addi t2, zero, 0
222:
	lbu a2, 0(a0)
	lbu a3, 0(a1)
	xor a2, a2, a3
	or t2, t2, a2
	addi a0, a0, 1
	addi a1, a1, 1
	addi s6, s6, -1
	bnez s6, 222b
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

vg_mldsa44_verify_message_cached:
	.option push
	.option arch, +m, +c
	srli t1, a4, 8
	beqz t1, 20f
	addi a0, zero, 2
	j 21f
20:
	lui t2, 19
	addi t2, t2, 0
	add t2, a6, t2
	sd s0, 904(t2)
	sd s1, 912(t2)
	sd s2, 920(t2)
	sd s3, 928(t2)
	sd s4, 936(t2)
	sd s5, 944(t2)
	sd s6, 952(t2)
	sd s7, 960(t2)
	sd s8, 968(t2)
	sd ra, 976(t2)
	addi s0, a0, 0
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, a3, 0
	addi s4, a4, 0
	addi s5, a5, 0
	addi s6, a7, 0
	addi s7, a6, 0
	addi s8, t2, 0
	addi t0, zero, 0
	sb t0, 984(s8)
	sb s4, 985(s8)
	addi t0, zero, 0
	sd t0, 0(s8)
	sd t0, 8(s8)
	sd t0, 16(s8)
	sd t0, 24(s8)
	sd t0, 32(s8)
	sd t0, 40(s8)
	sd t0, 48(s8)
	sd t0, 56(s8)
	sd t0, 64(s8)
	sd t0, 72(s8)
	sd t0, 80(s8)
	sd t0, 88(s8)
	sd t0, 96(s8)
	sd t0, 104(s8)
	sd t0, 112(s8)
	sd t0, 120(s8)
	sd t0, 128(s8)
	sd t0, 136(s8)
	sd t0, 144(s8)
	sd t0, 152(s8)
	sd t0, 160(s8)
	sd t0, 168(s8)
	sd t0, 176(s8)
	sd t0, 184(s8)
	sd t0, 192(s8)
	addi a3, s6, 0
	addi a2, zero, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a4, zero, 64
	call {vg_keccak_absorb}
	addi a3, s8, 984
	addi a2, a0, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a4, zero, 2
	call {vg_keccak_absorb}
	addi a3, s3, 0
	addi a2, a0, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a4, s4, 0
	call {vg_keccak_absorb}
	addi a3, s1, 0
	addi a2, a0, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a4, s2, 0
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s8, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s8, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s8, 840
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	addi a0, s0, 0
	addi a1, s8, 840
	addi a2, s5, 0
	addi a3, s7, 0
	call {vg_mldsa44_verify}
	ld ra, 976(s8)
	ld s0, 904(s8)
	ld s1, 912(s8)
	ld s2, 920(s8)
	ld s3, 928(s8)
	ld s4, 936(s8)
	ld s5, 944(s8)
	ld s6, 952(s8)
	ld s7, 960(s8)
	ld s8, 968(s8)
21:
	ret
	.option pop
