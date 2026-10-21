module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.FastR2Doubles
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext

/-! # Short doubling leaves the prepared multiplier's modulus and caller intact -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem doubles_ready {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (bound : g.w ≤ 64) (odd : c % 2 = 1)
    (top : 2 ^ (64 * g.w - 1) ≤ c) :
    WP isa (VG.Impl.RsaKeyGen.X86.FastR2.doubles (modulus g.w) (g.array 2) (g.array 6)) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ g.w * 2 ^ (64 * g.w) % c ∧
      Outs g.W (phaseRanges g) s.mem t.mem ∧ Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t := by
  have apart := g.arrayBefore (i := 0) (j := 6) (by decide)
  have apart' : g.array 6 + 8 * g.w ≤ (modulus g.w).mo ∨
      (modulus g.w).mo + 8 * g.w ≤ g.array 6 := by
    right
    change slot g.w 0 + 8 * g.w ≤ g.array 6
    rw [Prepared.slot_eq]
    unfold Geometry.words at apart
    omega
  refine WP.mono (FastR2.doubles_ok S.scratch (Prepared.dynamicModulus v S.modulus)
    (Prepared.layout v) apart' bound odd top) fun t ⟨value, _, O, K⟩ => ?_
  change Outs g.W [(g.array 6, 8 * g.w), ((modulus g.w).tmp, 8 * g.w),
    (g.array 2, accLen (modulus g.w))] s.mem t.mem at O
  change Outs g.W [(g.array 6, 8 * g.w), (slot g.w 1, 8 * g.w),
    (g.array 2, accLen (modulus g.w))] s.mem t.mem at O
  rw [Prepared.slot_eq] at O
  have F := WorkspaceFrame.of_outs S.scratch.nowrap O
  refine ⟨⟨Prepared.keepRanges v S.context K (by decide) O (fun _ mem => phase_header g mem),
    S.modulus.keep v F (fun r mem => Or.inl (by have := phase_header g mem; omega))
      (fun r mem => Or.inl (phase_candidate g mem)),
    S.caller.keepOuts K (by decide) O (fun r mem => phase_fits v mem),
    S.scratch.of_keeps K (by decide)⟩, ?_, O, K⟩
  unfold Geometry.words
  rw [← wordsVal_eq_val32]
  exact value

end VG.Proof.RsaKeyGen.X86.PreparedR2
