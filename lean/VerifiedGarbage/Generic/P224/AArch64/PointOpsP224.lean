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
    notes := ["The function runs the twelve products, two products by \
      `b` and the additions and subtractions of Algorithm 4 in their order, on four 64-bit words \
      modulo `p` read at byte 64, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and `umulh`; each reduction step multiplies the accumulator's low word by \
      `-p⁻¹ mod 2⁶⁴` and adds that multiple of `p`) with a final conditional subtraction, \
      its temporaries `t0`–`t5` at bytes 800 to 991 and the products' temporary area at bytes \
      128 to 159. It writes no vector register."]
    code := projAddP224
    verified := verified h.law h.inv }]

end VG.Generic.P224.AArch64.PointOpsP224
