module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-224's inversions modulo `p` and `n` on x86-64

`vg_p224_inv_mod_p` and `vg_p224_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-224's group law and inversions `h`, the variant
`Variants/P224/X86_64/Law.lean`, whose inversions' soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.P224.X86_64.InverseP224

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224.Inverse

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact :=
  ([false].map fun adx =>
    C.invPApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := (cfg adx).invFn (cfg adx).pPowI
      verified := p_verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] }) ++
  ([false].map fun adx =>
    C.invNApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := (cfg adx).invFn (cfg adx).nPowI
      verified := n_verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] })

end VG.Generic.P224.X86_64.InverseP224
