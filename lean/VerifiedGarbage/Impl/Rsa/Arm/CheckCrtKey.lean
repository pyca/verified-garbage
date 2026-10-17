module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck

/-! # `vg_rsa_check_crt_key` on ARMv7

`vg_rsa_check_crt_key(n, n_len, e, e_len, p, p_len, q, q_len, dp, dp_len,
dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the first four arguments
in `r0`–`r3`, the others on the stack, the working space at `sp + 40`. The
checks are `Impl/Rsa/Arm/KeyCheck.lean`'s `crtBody`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.CheckCrtKey
open VG VG.Arm VG.Impl.Rsa.Arm.KeyCheck

/-- The numbers on the stack: `p`, `q`, `dP`, `dQ` and `qInv`. -/
def args : List (Nat × Nat) := [(0, aP), (8, aQ), (16, aDP), (24, aDQ), (32, aQI)]

/-- `vg_rsa_check_crt_key`. -/
def code : Prog isa := fn 40 args crtBody

end VG.Impl.Rsa.Arm.CheckCrtKey
