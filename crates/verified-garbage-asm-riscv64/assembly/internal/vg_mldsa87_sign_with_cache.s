// The functions of `src/internal/vg_mldsa87_sign_with_cache.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_sign_with_cache:
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
	addi t2, zero, 0
	sltu t0, t2, a6
	sub t0, t2, t0
	and s3, a5, t0
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
	lui a1, 16
	addi a1, a1, -1024
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
	lui a1, 16
	addi a1, a1, 0
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
	lui a1, 16
	addi a1, a1, 1024
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
	lui a1, 17
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 5
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 6
	sb t0, 952(s11)
	addi t0, zero, 0
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 17
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
	lui a1, 18
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
	lui a1, 18
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
	lui a1, 18
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
	lui a1, 18
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 5
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 6
	sb t0, 952(s11)
	addi t0, zero, 1
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
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
	lui a1, 19
	addi a1, a1, 1024
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
	lui a1, 20
	addi a1, a1, -2048
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
	lui a1, 20
	addi a1, a1, -1024
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
	lui a1, 20
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 20
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 5
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 21
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 6
	sb t0, 952(s11)
	addi t0, zero, 2
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 21
	addi a1, a1, -1024
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
	lui a1, 21
	addi a1, a1, 0
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
	lui a1, 21
	addi a1, a1, 1024
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
	lui a1, 22
	addi a1, a1, -2048
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
	lui a1, 22
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 22
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 5
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 22
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 6
	sb t0, 952(s11)
	addi t0, zero, 3
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, -2048
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
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, -1024
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
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 0
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
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
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
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 24
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 24
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 5
	sb t0, 952(s11)
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 24
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 6
	sb t0, 952(s11)
	addi t0, zero, 4
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 24
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
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 25
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
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 25
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
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 25
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
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 25
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 26
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 5
	sb t0, 952(s11)
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 26
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 6
	sb t0, 952(s11)
	addi t0, zero, 5
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 26
	addi a1, a1, 0
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
	addi t0, zero, 6
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 26
	addi a1, a1, 1024
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
	addi t0, zero, 6
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 27
	addi a1, a1, -2048
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
	addi t0, zero, 6
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 27
	addi a1, a1, -1024
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
	addi t0, zero, 6
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 27
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 6
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 27
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 5
	sb t0, 952(s11)
	addi t0, zero, 6
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 28
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 6
	sb t0, 952(s11)
	addi t0, zero, 6
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 28
	addi a1, a1, -1024
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
	addi t0, zero, 7
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 28
	addi a1, a1, 0
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
	addi t0, zero, 7
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 28
	addi a1, a1, 1024
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
	addi t0, zero, 7
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 29
	addi a1, a1, -2048
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
	addi t0, zero, 7
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 29
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 4
	sb t0, 952(s11)
	addi t0, zero, 7
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 29
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 5
	sb t0, 952(s11)
	addi t0, zero, 7
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 29
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 1
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_rej_ntt_poly}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	addi t0, zero, 6
	sb t0, 952(s11)
	addi t0, zero, 7
	sb t0, 953(s11)
	lui a0, 0
	addi a0, a0, 920
	add a0, s11, a0
	lui a1, 30
	addi a1, a1, -2048
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
	bnez s3, 25f
	lui a0, 0
	addi a0, a0, 128
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 10
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 10
	addi a0, a0, 0
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
	lui a4, 10
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 10
	addi a0, a0, 1024
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
	lui a4, 11
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 11
	addi a0, a0, -2048
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
	lui a4, 11
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 11
	addi a0, a0, -1024
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
	lui a4, 11
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 11
	addi a0, a0, 0
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
	lui a4, 11
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 11
	addi a0, a0, 1024
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
	lui a4, 12
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 12
	addi a0, a0, -2048
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
	lui a4, 12
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 12
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 896
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 12
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 12
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 992
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 12
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 12
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1088
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 13
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 13
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1184
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 13
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 13
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1280
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 13
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 13
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1376
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 13
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 13
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1472
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 96
	lui a2, 0
	addi a2, a2, 2
	lui a3, 0
	addi a3, a3, 2
	lui a4, 14
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 14
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1568
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 14
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 14
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 0
	addi a0, a0, 1984
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 14
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 14
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 1
	addi a0, a0, -1696
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 14
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 14
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 1
	addi a0, a0, -1280
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 15
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 15
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 1
	addi a0, a0, -864
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 15
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 15
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 1
	addi a0, a0, -448
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 15
	addi a4, a4, 0
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 15
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 1
	addi a0, a0, -32
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 15
	addi a4, a4, 1024
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 15
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 1
	addi a0, a0, 384
	add a0, s10, a0
	lui a1, 0
	addi a1, a1, 416
	lui a2, 1
	addi a2, a2, -1
	lui a3, 1
	addi a3, a3, 0
	lui a4, 16
	addi a4, a4, -2048
	add a4, s11, a4
	call {vg_mldsa_bit_unpack}
	lui a0, 16
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	j 26f
25:
	lui a0, 0
	addi a0, a0, 0
	add a0, s3, a0
	lui a1, 10
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, -1024
27:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 27b
26:
	addi s7, zero, 0
	addi s5, zero, 814
28:
	addi a0, s7, 0
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, 0
	lui a2, 5
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 6
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
	lui a0, 6
	addi a0, a0, 1024
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
	lui a1, 128
	addi a1, a1, 0
	lui a2, 5
	addi a2, a2, -1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 1024
210:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	lui a0, 7
	addi a0, a0, -2048
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
	lui a1, 128
	addi a1, a1, 0
	lui a2, 5
	addi a2, a2, 0
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 1024
211:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 211b
	lui a0, 7
	addi a0, a0, -1024
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
	lui a1, 128
	addi a1, a1, 0
	lui a2, 5
	addi a2, a2, 1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 5
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 0
	add a1, s11, a1
	addi a2, zero, 1024
212:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 212b
	lui a0, 7
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 4
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, 0
	lui a2, 6
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 7
	addi a1, a1, 1024
	add a1, s11, a1
	addi a2, zero, 1024
213:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 213b
	lui a0, 7
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 5
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, 0
	lui a2, 6
	addi a2, a2, -1024
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, -2048
	add a1, s11, a1
	addi a2, zero, 1024
214:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 214b
	lui a0, 8
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	addi a0, s7, 6
	sb a0, 1024(s11)
	srli a0, a0, 8
	sb a0, 1025(s11)
	lui a0, 0
	addi a0, a0, 960
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, 0
	lui a2, 6
	addi a2, a2, 0
	add a2, s11, a2
	lui a3, 1
	addi a3, a3, -1024
	add a3, s11, a3
	call {vg_mldsa_expand_mask_poly}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, -1024
	add a1, s11, a1
	addi a2, zero, 1024
215:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	lui a0, 8
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 16
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 17
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 18
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 19
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 20
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 20
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 20
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 20
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 21
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 21
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 21
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 21
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 22
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 22
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 22
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 22
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 23
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 24
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 24
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 24
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 24
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 25
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 25
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 25
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 25
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 26
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 26
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 26
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 26
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 27
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 27
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 27
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 27
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 28
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 28
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 28
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 6
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_ntt}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 28
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 29
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 29
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 0
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 29
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 7
	addi a2, a2, 1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 29
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 30
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 8
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_multiply_add_ntt}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -1024
	add a1, s11, a1
	call {vg_mldsa_inv_ntt}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -2048
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1920
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1792
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1664
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1536
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1408
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1280
	add a2, s11, a2
	lui a3, 0
	addi a3, a3, 128
	call {vg_mldsa_simple_bit_pack}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -2048
	add a2, s11, a2
	call {vg_mldsa_high_bits}
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 15
	lui a2, 1
	addi a2, a2, -1152
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
	addi a4, zero, 1024
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
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	lui a0, 0
	addi a0, a0, 1040
	add a0, s11, a0
	lui a1, 0
	addi a1, a1, 64
	lui a2, 0
	addi a2, a2, 60
	lui a3, 1
	addi a3, a3, 1024
	add a3, s11, a3
	lui a4, 1
	addi a4, a4, -1024
	add a4, s11, a4
	call {vg_mldsa_sample_in_ball}
	slli a0, a0, 32
	srli a0, a0, 32
	bnez a0, 216f
	addi s4, zero, 0
	addi s5, zero, 1
	j 217f
216:
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
	lui a2, 10
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
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -120
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 218f
	j 219f
218:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 10
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
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -120
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 220f
	j 221f
220:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 11
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
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -120
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
	lui a2, 11
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
	lui a0, 5
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 5
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -120
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
	lui a2, 11
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
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -120
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
	lui a2, 11
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
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -120
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 228f
	j 229f
228:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 12
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
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -120
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 230f
	j 231f
230:
231:
229:
227:
225:
223:
221:
219:
	bnez s4, 232f
	j 233f
232:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 12
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
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -376
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 234f
	j 235f
234:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 12
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
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -376
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 236f
	j 237f
236:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 12
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
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -376
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 238f
	j 239f
238:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 13
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
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -376
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 240f
	j 241f
240:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 13
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
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -376
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 242f
	j 243f
242:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 13
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
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -376
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 244f
	j 245f
244:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 13
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
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -376
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 246f
	j 247f
246:
	lui a0, 2
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 14
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
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, -2048
	add a1, s11, a1
	call {vg_mldsa_sub}
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -256
	lui a2, 2
	addi a2, a2, -1024
	add a2, s11, a2
	call {vg_mldsa_low_bits}
	lui a0, 2
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 64
	addi a1, a1, -376
	call {vg_mldsa_norm_lt}
	slli a0, a0, 32
	srli a0, a0, 32
	and s4, s4, a0
	bnez s4, 248f
	j 249f
248:
249:
247:
245:
243:
241:
239:
237:
235:
	bnez s4, 250f
	j 251f
250:
	lui a0, 2
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 14
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
	lui a1, 64
	addi a1, a1, -256
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
252:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 252b
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
	lui a0, 8
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
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
	lui a2, 14
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
	lui a1, 64
	addi a1, a1, -256
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
253:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 253b
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
	lui a0, 8
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 8
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
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
	lui a2, 14
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
	lui a1, 64
	addi a1, a1, -256
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
254:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 254b
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
	lui a0, 9
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
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
	lui a2, 15
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
	lui a1, 64
	addi a1, a1, -256
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
255:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 255b
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
	lui a0, 9
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 3
	addi a3, a3, 1024
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
	lui a2, 15
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
	lui a1, 64
	addi a1, a1, -256
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
256:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 256b
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
	lui a0, 9
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, 0
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 4
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
	lui a2, 15
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
	lui a1, 64
	addi a1, a1, -256
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
257:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 257b
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
	lui a0, 9
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 9
	addi a1, a1, 1024
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 4
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
	lui a2, 15
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
	lui a1, 64
	addi a1, a1, -256
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
258:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 258b
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
	lui a0, 10
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -2048
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 4
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
	lui a2, 16
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
	lui a1, 64
	addi a1, a1, -256
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
259:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 259b
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
	lui a0, 10
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 2
	addi a1, a1, 0
	add a1, s11, a1
	call {vg_mldsa_add}
	lui a0, 2
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 10
	addi a1, a1, -1024
	add a1, s11, a1
	lui a2, 64
	addi a2, a2, -256
	lui a3, 4
	addi a3, a3, 1024
	add a3, s11, a3
	call {vg_mldsa_make_hint}
	slli a0, a0, 32
	srli a0, a0, 32
	add s6, s6, a0
	addi a0, s6, -76
	srli a0, a0, 63
	and s4, s4, a0
251:
233:
	bnez s4, 260f
	addi s7, s7, 7
	j 261f
260:
	addi s5, zero, 1
261:
217:
	addi s5, s5, -1
	bnez s5, 28b
	bnez s4, 262f
	j 263f
262:
	addi a0, s11, 1040
	addi a1, s8, 0
	addi a2, zero, 64
264:
	lbu a3, 0(a0)
	sb a3, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 264b
	lui a0, 5
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -1
	lui a2, 128
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 64
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 640
	call {vg_mldsa_bit_pack}
	lui a0, 5
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -1
	lui a2, 128
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 704
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 640
	call {vg_mldsa_bit_pack}
	lui a0, 5
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -1
	lui a2, 128
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1344
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 640
	call {vg_mldsa_bit_pack}
	lui a0, 5
	addi a0, a0, 1024
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -1
	lui a2, 128
	addi a2, a2, 0
	lui a3, 0
	addi a3, a3, 1984
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 640
	call {vg_mldsa_bit_pack}
	lui a0, 6
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -1
	lui a2, 128
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -1472
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 640
	call {vg_mldsa_bit_pack}
	lui a0, 6
	addi a0, a0, -1024
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -1
	lui a2, 128
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -832
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 640
	call {vg_mldsa_bit_pack}
	lui a0, 6
	addi a0, a0, 0
	add a0, s11, a0
	lui a1, 128
	addi a1, a1, -1
	lui a2, 128
	addi a2, a2, 0
	lui a3, 1
	addi a3, a3, -192
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 640
	call {vg_mldsa_bit_pack}
	lui a0, 3
	addi a0, a0, -2048
	add a0, s11, a0
	lui a1, 1
	addi a1, a1, -2048
	lui a2, 0
	addi a2, a2, 75
	lui a3, 1
	addi a3, a3, 448
	add a3, s8, a3
	lui a4, 0
	addi a4, a4, 83
	call {vg_mldsa_hint_bit_pack}
263:
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
