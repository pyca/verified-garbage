module
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseCfgLit

public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP512r1's inversions modulo `p` and `n` on x86-64 -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.X86_64.InverseBrainpoolP512r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.BrainpoolP512r1.Inverse

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact :=
  [C.invPApi.artifact X86_64.target {
      code := cfg.invFn cfg.pPowI
      verified := p_verified h.inv },
    C.invNApi.artifact X86_64.target {
      code := cfg.invFn cfg.nPowI
      verified := n_verified h.inv }]

end VG.Generic.BrainpoolP512r1.X86_64.InverseBrainpoolP512r1
