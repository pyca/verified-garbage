module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
import VerifiedGarbage.Proof.Rsa.AArch64.InvFinish

/-! # The proofs supplied at the RSA registrations on AArch64

The inverse's contract (`InvLaw`), proved in `InvFinish.lean`.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

instance invLaw : InvLaw where
  inverse_ok := inverse_ok

end VG.Proof.Rsa.AArch64
