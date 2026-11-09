// The functions of `src/mldsa87.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_keygen:
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
	addi t0, zero, 8
	sb t0, 920(s11)
	addi t0, zero, 7
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
	addi t0, zero, 4
	sb t0, 1184(s11)
	addi t0, zero, 0
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
	addi t0, zero, 5
	sb t0, 1184(s11)
	addi t0, zero, 0
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
	addi t0, zero, 6
	sb t0, 1184(s11)
	addi t0, zero, 0
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
	addi t0, zero, 0
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
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 1
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
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 1
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
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 1
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
	addi t0, zero, 4
	sb t0, 1184(s11)
	addi t0, zero, 1
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
	addi t0, zero, 5
	sb t0, 1184(s11)
	addi t0, zero, 1
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
	addi t0, zero, 6
	sb t0, 1184(s11)
	addi t0, zero, 1
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
	addi t0, zero, 0
	sb t0, 1184(s11)
	addi t0, zero, 2
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
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 2
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
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 5
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
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 5
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
	addi t0, zero, 4
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 6
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
	addi t0, zero, 5
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 6
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
	addi t0, zero, 6
	sb t0, 1184(s11)
	addi t0, zero, 2
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 6
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
	addi t0, zero, 0
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 6
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
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 7
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
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 7
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
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 7
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
	lui a1, 7
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
226:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 226b
	addi t0, zero, 4
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 7
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
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
227:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 227b
	addi t0, zero, 5
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 8
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
	lui a1, 8
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
228:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 228b
	addi t0, zero, 6
	sb t0, 1184(s11)
	addi t0, zero, 3
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 8
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
	lui a1, 8
	addi a1, a1, -1024
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
	sb t0, 1184(s11)
	addi t0, zero, 4
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 8
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
	lui a1, 8
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
	sb t0, 1184(s11)
	addi t0, zero, 4
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 8
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
	lui a1, 8
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
	sb t0, 1184(s11)
	addi t0, zero, 4
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 9
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
	lui a1, 9
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
	sb t0, 1184(s11)
	addi t0, zero, 4
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 9
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
	lui a1, 9
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
	sb t0, 1184(s11)
	addi t0, zero, 4
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 9
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
	lui a1, 9
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
	addi t0, zero, 5
	sb t0, 1184(s11)
	addi t0, zero, 4
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 9
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
	lui a1, 9
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
235:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 235b
	addi t0, zero, 6
	sb t0, 1184(s11)
	addi t0, zero, 4
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 10
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
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
236:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 236b
	addi t0, zero, 0
	sb t0, 1184(s11)
	addi t0, zero, 5
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 10
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
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
237:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 237b
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 5
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 10
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
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
238:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 238b
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 5
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 10
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
	lui a1, 10
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
239:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 239b
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 5
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 11
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
	lui a1, 11
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
240:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 240b
	addi t0, zero, 4
	sb t0, 1184(s11)
	addi t0, zero, 5
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 11
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
	lui a1, 11
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
241:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 241b
	addi t0, zero, 5
	sb t0, 1184(s11)
	addi t0, zero, 5
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 11
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
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
242:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 242b
	addi t0, zero, 6
	sb t0, 1184(s11)
	addi t0, zero, 5
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 11
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
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
243:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 243b
	addi t0, zero, 0
	sb t0, 1184(s11)
	addi t0, zero, 6
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 12
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
	lui a1, 12
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
244:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 244b
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 6
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 12
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
	lui a1, 12
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
245:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 245b
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 6
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 12
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
	lui a1, 12
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
246:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 246b
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 6
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 12
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
	lui a1, 12
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
247:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 247b
	addi t0, zero, 4
	sb t0, 1184(s11)
	addi t0, zero, 6
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 13
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
	lui a1, 13
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
248:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 248b
	addi t0, zero, 5
	sb t0, 1184(s11)
	addi t0, zero, 6
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 13
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
	lui a1, 13
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
249:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 249b
	addi t0, zero, 6
	sb t0, 1184(s11)
	addi t0, zero, 6
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 13
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
	lui a1, 13
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
250:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 250b
	addi t0, zero, 0
	sb t0, 1184(s11)
	addi t0, zero, 7
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 13
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
	lui a1, 13
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
251:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 251b
	addi t0, zero, 1
	sb t0, 1184(s11)
	addi t0, zero, 7
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 14
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
	lui a1, 14
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
252:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 252b
	addi t0, zero, 2
	sb t0, 1184(s11)
	addi t0, zero, 7
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 14
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
	lui a1, 14
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
253:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 253b
	addi t0, zero, 3
	sb t0, 1184(s11)
	addi t0, zero, 7
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 14
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
	lui a1, 14
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
254:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 254b
	addi t0, zero, 4
	sb t0, 1184(s11)
	addi t0, zero, 7
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 14
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
	lui a1, 14
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
255:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 255b
	addi t0, zero, 5
	sb t0, 1184(s11)
	addi t0, zero, 7
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 15
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
	lui a1, 15
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
256:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 256b
	addi t0, zero, 6
	sb t0, 1184(s11)
	addi t0, zero, 7
	sb t0, 1185(s11)
	lui a0, 0
	addi a0, a0, 1152
	add a0, s11, a0
	lui a1, 15
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
	lui a1, 15
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
257:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 257b
	addi t0, zero, 0
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 15
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
	lui a1, 15
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
258:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 258b
	addi t0, zero, 1
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 15
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
	lui a1, 15
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
259:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 259b
	addi t0, zero, 2
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 16
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
	lui a1, 16
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
260:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 260b
	addi t0, zero, 3
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 16
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
	lui a1, 16
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
261:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 261b
	addi t0, zero, 4
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 16
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
	lui a1, 16
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
262:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 262b
	addi t0, zero, 5
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 16
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
	lui a1, 16
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
263:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 263b
	addi t0, zero, 6
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 17
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
	lui a1, 17
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
264:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 264b
	addi t0, zero, 7
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 17
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
	lui a1, 17
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
265:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 265b
	addi t0, zero, 8
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 17
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
	lui a1, 17
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
266:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 266b
	addi t0, zero, 9
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 17
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
	lui a1, 17
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
267:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 267b
	addi t0, zero, 10
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 18
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
	lui a1, 18
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
268:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 268b
	addi t0, zero, 11
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 18
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
	lui a1, 18
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 256
269:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 269b
	addi t0, zero, 12
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 18
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
	lui a1, 18
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 256
270:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 270b
	addi t0, zero, 13
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 18
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
	lui a1, 18
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 256
271:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 271b
	addi t0, zero, 14
	sb t0, 1280(s11)
	lui a0, 0
	addi a0, a0, 1216
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 19
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
	lui a1, 19
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 256
272:
	lwu a3, 0(a1)
	and a3, a3, t2
	sw a3, 0(a1)
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 272b
	addi a0, s11, 1024
	addi a1, s9, 0
	addi a2, zero, 32
273:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 273b
	addi a0, s11, 1024
	addi a1, s8, 0
	addi a2, zero, 32
274:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 274b
	addi a0, s11, 1120
	addi a1, s8, 32
	addi a2, zero, 32
275:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 275b
	lui a0, 15
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
	lui a0, 15
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
	lui a0, 16
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
	lui a0, 16
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
	lui a0, 16
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
	lui a0, 16
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
	lui a0, 17
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
	lui a0, 17
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
	lui a0, 17
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 896
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 17
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 992
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 18
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 1088
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 18
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 1184
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 18
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 1280
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 18
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 1376
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 19
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 2
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 1472
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 96
	call {vg_mldsa_bit_pack}
	lui a0, 15
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 15
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 16
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 16
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 16
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 16
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 17
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 17
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 19
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 19
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 32
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 19
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1568
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 17
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 19
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 19
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 352
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 19
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1984
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 17
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 19
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 19
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 672
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 19
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -1696
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 17
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 19
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 19
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 992
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 19
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -1280
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 17
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 19
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 19
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 1312
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 19
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -864
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 11
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 17
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 19
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 19
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 1632
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 19
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -448
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 12
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 17
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, 1024
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 19
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 19
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 0
	addi a2, a2, 1952
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 19
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -32
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 416
	call {vg_mldsa_bit_pack}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 13
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 15
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 14
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 15
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 16
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 15
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 17
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 19
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 19
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_power2round}
	lui a0, 19
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 1023
	lui a2, 1
	addi a2, a2, -1824
	add a2, s9, a2
	lui a3, 0
	addi a3, a3, 320
	call {vg_mldsa_simple_bit_pack}
	lui a0, 19
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1
	lui a2, 1
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, 384
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
	addi a4, zero, 1568
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

vg_mldsa87_pk_tr:
	.option push
	.option arch, +m, +c
	sd s3, 1288(a2)
	sd s4, 1296(a2)
	sd s5, 1304(a2)
	sd s6, 1312(a2)
	sd s7, 1320(a2)
	sd s8, 1328(a2)
	sd s9, 1336(a2)
	sd s10, 1344(a2)
	sd s11, 1352(a2)
	sd ra, 1360(a2)
	addi s10, a0, 0
	addi s9, a0, 0
	addi s8, a1, 0
	addi s11, a2, 0
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
	addi a4, zero, 1568
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a2, zero, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, s8, 0
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

vg_mldsa87_prepare_verifying_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1072
	addi a3, sp, 0
	sd s8, 1024(a3)
	sd s9, 1032(a3)
	sd s10, 1040(a3)
	sd s11, 1048(a3)
	sd ra, 1056(a3)
	addi s8, a2, 0
	addi s9, a1, 0
	addi s10, a0, 0
	addi s11, a3, 0
	lui a0, 0
	addi a0, a0, 0
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s9, a1
	lui a2, 1
	addi a2, a2, -1504
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	lui a0, 0
	addi a0, a0, 32
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1504
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
21:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 21b
	lui a0, 0
	addi a0, a0, 352
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -480
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
22:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 22b
	lui a0, 0
	addi a0, a0, 672
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 544
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
23:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 23b
	lui a0, 0
	addi a0, a0, 992
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1568
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
24:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 24b
	lui a0, 0
	addi a0, a0, 1312
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -1504
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
25:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 25b
	lui a0, 0
	addi a0, a0, 1632
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -480
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
26:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 26b
	lui a0, 0
	addi a0, a0, 1952
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 544
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
27:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 27b
	lui a0, 1
	addi a0, a0, -1824
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_unpack_t1}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1568
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
28:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	ld ra, 1056(s11)
	ld s8, 1024(s11)
	ld s9, 1032(s11)
	ld s10, 1040(s11)
	ld s11, 1048(s11)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	addi sp, sp, 1072
	ret
	.option pop

vg_mldsa87_prepare_signing_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1072
	addi a3, sp, 0
	sd s8, 1024(a3)
	sd s9, 1032(a3)
	sd s10, 1040(a3)
	sd s11, 1048(a3)
	sd ra, 1056(a3)
	addi s8, a2, 0
	addi s9, a1, 0
	addi s10, a0, 0
	addi s11, a3, 0
	lui a0, 0
	addi a0, a0, 0
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s9, a1
	lui a2, 1
	addi a2, a2, 800
20:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	lui a0, 0
	addi a0, a0, 128
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 800
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
21:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 21b
	lui a0, 0
	addi a0, a0, 224
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1824
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
22:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 22b
	lui a0, 0
	addi a0, a0, 320
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -1248
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
23:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 23b
	lui a0, 0
	addi a0, a0, 416
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -224
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
24:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 24b
	lui a0, 0
	addi a0, a0, 512
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 800
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
25:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 25b
	lui a0, 0
	addi a0, a0, 608
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 1824
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
26:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 26b
	lui a0, 0
	addi a0, a0, 704
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, -1248
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
27:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 27b
	lui a0, 0
	addi a0, a0, 800
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, -224
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
28:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	lui a0, 0
	addi a0, a0, 896
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, 800
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
29:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 29b
	lui a0, 0
	addi a0, a0, 992
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 3
	addi a1, a1, 1824
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
210:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	lui a0, 0
	addi a0, a0, 1088
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, -1248
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
211:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 211b
	lui a0, 0
	addi a0, a0, 1184
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, -224
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
212:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 212b
	lui a0, 0
	addi a0, a0, 1280
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, 800
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
213:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 213b
	lui a0, 0
	addi a0, a0, 1376
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 4
	addi a1, a1, 1824
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
214:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 214b
	lui a0, 0
	addi a0, a0, 1472
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -1248
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
215:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	lui a0, 0
	addi a0, a0, 1568
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, -224
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
216:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 216b
	lui a0, 0
	addi a0, a0, 1984
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, 800
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
217:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 217b
	lui a0, 1
	addi a0, a0, -1696
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 5
	addi a1, a1, 1824
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
218:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 218b
	lui a0, 1
	addi a0, a0, -1280
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -1248
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
219:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 219b
	lui a0, 1
	addi a0, a0, -864
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, -224
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
220:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	lui a0, 1
	addi a0, a0, -448
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 800
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
221:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 221b
	lui a0, 1
	addi a0, a0, -32
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 6
	addi a1, a1, 1824
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
222:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 222b
	lui a0, 1
	addi a0, a0, 384
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 0
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 0
	add a1, s8, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -1248
	add a1, s9, a1
	lui a2, 0
	addi a2, a2, 1024
223:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 223b
	ld ra, 1056(s11)
	ld s8, 1024(s11)
	ld s9, 1032(s11)
	ld s10, 1040(s11)
	ld s11, 1048(s11)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	addi sp, sp, 1072
	ret
	.option pop

vg_mldsa87_sign:
	.option push
	.option arch, +m, +c
	addi sp, sp, -16
	sd ra, 8(sp)
	addi a5, a0, 0
	addi a6, zero, 0
	call {vg_mldsa87_sign_with_cache}
	ld ra, 8(sp)
	addi sp, sp, 16
	ret
	.option pop

vg_mldsa87_sign_message:
	.option push
	.option arch, +m, +c
	srli t1, a4, 8
	beqz t1, 20f
	addi a0, zero, 2
	j 21f
20:
	lui t2, 35
	addi t2, t2, 1024
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
	call {vg_mldsa87_sign}
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

vg_mldsa87_sign_message_prepared:
	.option push
	.option arch, +m, +c
	srli t1, a4, 8
	beqz t1, 20f
	addi a0, zero, 2
	j 21f
20:
	lui t2, 35
	addi t2, t2, 1024
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
	call {vg_mldsa87_sign_prepared}
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

vg_mldsa87_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -16
	sd ra, 8(sp)
	addi a4, a0, 0
	addi a5, zero, 0
	call {vg_mldsa87_verify_with_cache}
	ld ra, 8(sp)
	addi sp, sp, 16
	ret
	.option pop

vg_mldsa87_verify_message_cached:
	.option push
	.option arch, +m, +c
	srli t1, a4, 8
	beqz t1, 20f
	addi a0, zero, 2
	j 21f
20:
	lui t2, 35
	addi t2, t2, 1024
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
	call {vg_mldsa87_verify}
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

vg_mldsa87_verify_message_prepared:
	.option push
	.option arch, +m, +c
	srli t1, a4, 8
	beqz t1, 20f
	addi a0, zero, 2
	j 21f
20:
	lui t2, 35
	addi t2, t2, 1024
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
	call {vg_mldsa87_verify_prepared}
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
