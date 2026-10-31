module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.PointOpsVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-224's complete projective addition on AArch64

`vg_p224_proj_add` (`Spec/Weierstrass/PointOps.lean`), which P-224's
signature, public key derivation, ECDH and verification call for their
complete additions. A generic file (see `TCB/Emit.lean`) over P-224's group
law and inversions `h`, the variant `Variants/P224/AArch64/Law.lean`, which
gives Fermat's little theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the
contract.
-/

@[expose] public section

namespace VG.Generic.P224.AArch64.PointOpsP224

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P224.PointOps

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  C.projAddApi.artifact AArch64.target {
    code := projAddP224
    verified := verified h.law h.inv }]

end VG.Generic.P224.AArch64.PointOpsP224
