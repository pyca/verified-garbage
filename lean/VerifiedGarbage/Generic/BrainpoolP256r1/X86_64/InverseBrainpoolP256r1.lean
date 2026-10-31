module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.InverseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.InverseLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP256r1's inversions modulo `p` and `n` on x86-64

`vg_brainpoolp256r1_inv_mod_p` and `vg_brainpoolp256r1_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over brainpoolP256r1's group law and inversions `h`, the variant
`Variants/BrainpoolP256r1/X86_64/Law.lean`, whose inversions' soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.X86_64.InverseBrainpoolP256r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.BrainpoolP256r1.Inverse

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact :=
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

end VG.Generic.BrainpoolP256r1.X86_64.InverseBrainpoolP256r1
