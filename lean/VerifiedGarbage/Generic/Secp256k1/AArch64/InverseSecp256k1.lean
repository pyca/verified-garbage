module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # secp256k1's inversions modulo `p` and `n` on AArch64 -/

@[expose] public section

namespace VG.Generic.Secp256k1.AArch64.InverseSecp256k1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1.Inverse

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    code := secp256k1.invFn secp256k1.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    code := secp256k1.invFn secp256k1.nPowI
    verified := n_verified h.inv }]

end VG.Generic.Secp256k1.AArch64.InverseSecp256k1
