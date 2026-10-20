module
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.Rsa.CrtValuesMath

/-! # `vg_rsa_crt_values` on ARMv7: the checks are `crtKey`

`crtKey_masked`: with the mask of the checks computed as `vg_rsa_crt_values`
computes them (`p` odd, `n / p = q`, `n mod p = 0`, and the gcd that
`inverse` finds modulo `p | 1` is 1), `crtKey` is the values computed if the
mask is set, and nothing otherwise.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG.Spec.Rsa

alias pq_iff := VG.Proof.Rsa.CrtValues.pq_iff
alias odd_of_mul := VG.Proof.Rsa.CrtValues.odd_of_mul
alias crtKey_masked := VG.Proof.Rsa.CrtValues.crtKey_masked

end VG.Proof.Rsa.Arm.CrtValues
