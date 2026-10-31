module

-- shake: keep (preserves the GHASH contract and memory helper interface for callers)
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Base
public import VerifiedGarbage.Impl.Gcm.PPC64LE

/-! # PPC64LE GHASH contract interface

Callers take the baseline implementation's correctness and constant-time
proofs as a hypothesis. Registration supplies the proved implementation,
so the callers do not import its polynomial algebra.
-/

@[expose] public section
namespace VG.Proof.Gcm.PPC64LE
open VG VG.PPC64LE

class GhashLaw : Prop where
  correct : ∀ s, Proof.Gcm.ghashPPC64LE.pre s →
    ∃ t s', Exec isa Impl.Gcm.PPC64LE.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashPPC64LE.post s s'
  ct : ConstantTime isa Proof.Gcm.ghashPPC64LE.pre Proof.Gcm.ghashPPC64LE.pub Impl.Gcm.PPC64LE.ghash

theorem ghash_correct [GhashLaw] (s : State) (h : Proof.Gcm.ghashPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Gcm.PPC64LE.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashPPC64LE.post s s' := GhashLaw.correct s h

theorem ghash_ct [GhashLaw] :
    ConstantTime isa Proof.Gcm.ghashPPC64LE.pre Proof.Gcm.ghashPPC64LE.pub Impl.Gcm.PPC64LE.ghash :=
  GhashLaw.ct

end VG.Proof.Gcm.PPC64LE
