module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP512r1's inversions modulo `p` and `n` on AArch64

`vg_brainpoolp512r1_inv_mod_p` and `vg_brainpoolp512r1_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call.
A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law and inversions
`h`, the variant `Variants/BrainpoolP512r1/AArch64/Law.lean`, whose inversions'
soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AArch64.InverseBrainpoolP512r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Inverse

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    code := brainpoolp512r1.invFn brainpoolp512r1.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    code := brainpoolp512r1.invFn brainpoolp512r1.nPowI
    verified := n_verified h.inv }]

end VG.Generic.BrainpoolP512r1.AArch64.InverseBrainpoolP512r1
