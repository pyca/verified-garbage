module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyCheck

/-! # `vg_rsa_check_key` on RISC-V

`vg_rsa_check_key(n = a0, n_len = a1, e = a2, e_len = a3, d = a4,
d_len = a5, p = a6, p_len = a7, q, q_len, dp, dp_len, dq, dq_len, qinv,
qinv_len, scratch, scratch_len)`, the last ten on the stack. The checks are
`Impl/Rsa/RISCV64/KeyCheck.lean`'s: those of `vg_rsa_check_crt_key`, then
those of `d`.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.CheckKey

open VG.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.KeyCheck

/-- `n`, `n_len`, `p`, `p_len`, `d`, `d_len`, `e` and `e_len` kept, then
`q`, `q_len`, `dp`, `dq` and `qinv` from the stack. -/
def moves : List Instr :=
  [mov .s1 .a0, mov .s2 .a1, mov .s3 .a6, mov .s4 .a7, mov .a0 .a4, mov .a1 .a5, mov .a4 .a2,
    mov .a5 .a3, .addSp .t0 0, .load .d .s5 .t0 0, .load .d .s6 .t0 8, .load .d .a2 .t0 16,
    .load .d .a3 .t0 32, .load .d .a6 .t0 48]

/-- `n`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` read. -/
def loads : List (Prog isa) :=
  [load aN .s1 .s2, load aD .a0 .a1, load aP .s3 .s4, load aQ .s5 .s6, load aDP .a2 .s4,
    load aDQ .a3 .s6, load aQI .a6 .s4]

/-- `vg_rsa_check_key`. -/
def code : Prog isa := fn 64 moves loads (.block keepLen :: start ++ crtChecks ++ dChecks)

end VG.Impl.Rsa.RISCV64.CheckKey
