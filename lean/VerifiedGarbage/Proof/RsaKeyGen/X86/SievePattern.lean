module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter

/-! # Timing may relate different passing candidates or equal rejected candidates -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.Proof.RsaKeyGen

theorem samePattern_refl (g : Geometry) (c : Nat) : SamePattern g c c := fun _ _ => rfl

theorem samePattern_clear {g : Geometry} {c d : Nat}
    (C : trialPrefix c g.limit = false) (D : trialPrefix d g.limit = false) : SamePattern g c d := by
  intro i index
  have clearC := List.any_eq_false.mp C i (List.mem_range.mpr index)
  have clearD := List.any_eq_false.mp D i (List.mem_range.mpr index)
  have cbit : dividesAt c i = false := Bool.eq_false_iff.mpr clearC
  have dbit : dividesAt d i = false := Bool.eq_false_iff.mpr clearD
  rw [cbit, dbit]

theorem samePattern_passing {g : Geometry} {c d : Nat}
    (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w)
    (cLarge : 8161 < c) (dLarge : 8161 < d)
    (C : Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c = false)
    (D : Spec.RsaKeyGen.obviouslyComposite (64 * g.w) d = false) : SamePattern g c d := by
  apply samePattern_clear
  · rw [length]
    exact (trialPrefix_spec cLarge).trans C
  · rw [length]
    exact (trialPrefix_spec dLarge).trans D

end VG.Proof.RsaKeyGen.X86.Sieve
