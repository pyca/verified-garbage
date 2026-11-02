module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyCheck

/-! # `vg_rsa_check_crt_key` on RISC-V

`vg_rsa_check_crt_key(n = a0, n_len = a1, e = a2, e_len = a3, p = a4,
p_len = a5, q = a6, q_len = a7, dp, dp_len, dq, dq_len, qinv, qinv_len,
scratch, scratch_len)`, the last eight on the stack. The checks are
`Impl/Rsa/RISCV64/KeyCheck.lean`'s.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.CheckCrtKey

open VG.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.KeyCheck

/-- `n`, `n_len`, `p`, `p_len`, `q`, `q_len`, `e` and `e_len` kept, then
`dp`, `dq` and `qinv` from the stack. -/
def moves : List Instr :=
  [mov .s1 .a0, mov .s2 .a1, mov .s3 .a4, mov .s4 .a5, mov .s5 .a6, mov .s6 .a7, mov .a4 .a2,
    mov .a5 .a3, .addSp .t0 0, .load .d .a2 .t0 0, .load .d .a3 .t0 16, .load .d .a6 .t0 32]

/-- `n`, `p`, `q`, `dP`, `dQ` and `qInv` read. -/
def loads : List (Prog isa) :=
  [load aN .s1 .s2, load aP .s3 .s4, load aQ .s5 .s6, load aDP .a2 .s4, load aDQ .a3 .s6,
    load aQI .a6 .s4]

/-- `vg_rsa_check_crt_key`. -/
def code : Prog isa := fn 48 moves loads (start ++ crtChecks)

end VG.Impl.Rsa.RISCV64.CheckCrtKey
