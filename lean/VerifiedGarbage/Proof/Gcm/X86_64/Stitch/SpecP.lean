import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Spec.Gcm.Precomputed

/-!
# Interleaved loops with the powers of the hash subkey in the key context

Untrusted: everything here is checked by Lean. `SPreP s₀`: `SPre s₀`, and the
key context, of 1024 bytes, holds the powers of its hash subkey
(`Spec.Gcm.PowersRepr`), apart from the data and the working space, which the
loops write. `StitchOkP` is `StitchOk` from it: loops that read the powers
instead of computing them.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64

/-- The key context with its powers: 1024 bytes. -/
abbrev kPR (s₀ : State) : Region := ⟨kp s₀, 1024⟩

structure SPreP (s₀ : State) : Prop where
  base : SPre s₀
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 1024
  wrap_k : (kp s₀).toNat + 1024 ≤ 2 ^ 64
  d_k : (dR s₀).Disjoint (kPR s₀)
  p_k : (pR s₀).Disjoint (kPR s₀)
  pow : Spec.Gcm.PowersRepr s₀.mem (kp s₀)

/-- Interleaved loops `enc` and `dec` that read the powers meet the contracts. -/
def StitchOkP (enc dec : Prog isa) : Prop :=
  (∀ s₀, SPreP s₀ → WP isa enc s₀ (EPost s₀)) ∧ (∀ s₀, SPreP s₀ → WP isa dec s₀ (DPost s₀))

end VG.Proof.Gcm.X86_64.Stitch
