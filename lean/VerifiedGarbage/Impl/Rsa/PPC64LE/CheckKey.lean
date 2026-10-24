module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyCheck

/-! # `vg_rsa_check_key` on PPC64LE

`vg_rsa_check_key(n, n_len, e, e_len, d, d_len, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the first eight
arguments in `r3`–`r10`, the others on the stack (`q` is the 0th). The checks
are `Impl/Rsa/PPC64LE/KeyCheck.lean`'s: those of `vg_rsa_check_crt_key`,
then those of `d`.
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.CheckKey

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.KeyCheck

/-- `n`, `n_len`, `d`, `d_len`, `p` and `p_len` kept. -/
def moves : List Instr :=
  [.addi .r14 .r3 0, .addi .r15 .r4 0, .addi .r16 .r7 0, .addi .r17 .r8 0, .addi .r18 .r9 0,
    .addi .r19 .r10 0]

/-- `q`, `q_len`, `dp`, `dq` and `qinv` from the stack. -/
def stk : List Instr :=
  CrtValues.stackArg .r20 0 ++ CrtValues.stackArg .r21 1 ++ CrtValues.stackArg .r22 2 ++
    CrtValues.stackArg .r23 4 ++ CrtValues.stackArg .r26 6

/-- `n`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` read. -/
def loads : List (Prog isa) :=
  loadR .r14 .r15 aN ++ loadR .r16 .r17 aD ++ loadR .r18 .r19 aP ++ loadR .r20 .r21 aQ ++
    loadR .r22 .r19 aDP ++ loadR .r23 .r21 aDQ ++ loadR .r26 .r19 aQI

/-- `vg_rsa_check_key`. -/
def code : Prog isa := fn 8 moves stk loads (start ++ crtChecks ++ dChecks)

end VG.Impl.Rsa.PPC64LE.CheckKey
