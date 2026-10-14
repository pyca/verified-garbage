module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# `vg_rsa_public_checked` for its callers on x86-64

The implementation of `vg_rsa_public_checked` that `vg_rsa_pkcs1_verify` and
`vg_rsa_pkcs1_recover` call (`PubImpl`), with what they need of it.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64

/-- `vg_rsa_public_checked`. -/
def pubChecked : PubImpl where
  name := Spec.Rsa.publicCheckedApi.name
  code := Impl.Rsa.X86_64.Checked.publicChecked
  ok := Proof.Rsa.X86_64.publicChecked_correct
  ct := Proof.Rsa.X86_64.publicChecked_constantTime
  nosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)

end VG.Proof.RsaPkcs1Sig.X86_64
