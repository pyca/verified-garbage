module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck

/-! # `vg_rsa_check_key` on ARMv7

`vg_rsa_check_key(n, n_len, e, e_len, d, d_len, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the first four
arguments in `r0`–`r3`, the others on the stack, the working space at
`sp + 48`. The checks are `Impl/Rsa/Arm/KeyCheck.lean`'s `keyBody`: those of
`vg_rsa_check_crt_key`, then those of `d`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.CheckKey
open VG VG.Arm VG.Impl.Rsa.Arm.KeyCheck

/-- The numbers on the stack: `d`, `p`, `q`, `dP`, `dQ` and `qInv`. -/
def args : List (Nat × Nat) := [(0, aD), (8, aP), (16, aQ), (24, aDP), (32, aDQ), (40, aQI)]

/-- `vg_rsa_check_key`. -/
def code : Prog isa := fn 48 args keyBody

end VG.Impl.Rsa.Arm.CheckKey
