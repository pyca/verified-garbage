module
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashState
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashOne

/-! # Every p-candidate contribution is written once in descending significance -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def ContributionPlan.digest {H : Hash} (G : ContributionPlan) (K : HashOK H) (j : Nat) : List Byte :=
  K.SH.H.hash (Spec.Dsa.encodeBE G.seed.length (Spec.Dsa.decodeBE G.seed + G.offset + j))

def ContributionPlan.allWrites {H : Hash} (G : ContributionPlan) (K : HashOK H) : List Region :=
  (List.range (G.count + 1)).flatMap (G.writes K)

theorem pHashOneReady_ok {H : Hash} {K : HashOK H} {G : ContributionPlan} {s : State} {j : Nat}
    (L : ContributionLayout K G) (R : ContributionReady K G s) (hj : j ≤ G.count) :
    WP isa (pHashOne H G.seed.length G.count j) s fun t =>
      ContributionReady K G t ∧ Spec.Rsa.bytesAt t.mem ((G.output j).setWidth 64) G.seed.length = G.digest K j ∧
      Frame (G.writes K j) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have apart : ∀ i < G.seed.length, ∀ k < G.seed.length,
      off (G.source.setWidth 64) i ≠ off (G.wrapped.setWidth 64) k := by
    intro i hi k hk eq
    apply L.sourceWrapped (off (G.source.setWidth 64) i)
      (Offset.contains_base _ hi (by have := L.lengthBound; omega))
    rw [eq]
    exact Offset.contains_base _ hk (by have := L.lengthBound; omega)
  refine WP.mono (pHashOne_ok K G.seed R.frame R.source R.wrapped R.hashes R.scratch R.offset
    (R.resources j hj) L.lengthBound (by have := L.offsetBound; omega) L.sourceFit R.sourceRead R.wrappedWrite R.bytes apart)
    fun t ⟨value, O, Ke⟩ => ?_
  rw [R.stack] at O
  change Frame (G.writes K j) s.mem t.mem at O
  refine ⟨R.keep L hj O Ke (by decide), ?_, O, Ke⟩
  rw [L.digestLength, L.finalLength] at value
  rw [List.take_of_length_le (by simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]; exact Nat.le_refl _)] at value
  exact value

theorem pHashPrefix_ok {H : Hash} {K : HashOK H} {G : ContributionPlan} {s : State}
    (L : ContributionLayout K G) (R : ContributionReady K G s) {k : Nat} (bound : k ≤ G.count + 1) :
    WP isa (pHashPrefix H G.seed.length G.count k) s fun t => ContributionReady K G t ∧
      (∀ j < k, Spec.Rsa.bytesAt t.mem ((G.output j).setWidth 64) G.seed.length = G.digest K j) ∧
      Frame (G.allWrites K) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  induction k with
  | zero => exact WP.block_nil ⟨R, by intro j hj; omega, Frame.refl _ _, Keeps.refl _ _⟩
  | succ k ih =>
    unfold pHashPrefix
    refine WP.seq (WP.mono (ih (by omega)) fun a ⟨Ra, prior, Fa, Ka⟩ => ?_)
    refine WP.mono (pHashOneReady_ok L Ra (j := k) (by omega)) fun t ⟨Rt, last, Ft, Kt⟩ => ?_
    refine ⟨Rt, ?_, Fa.trans (Ft.mono ?_), Ka.trans Kt⟩
    · intro j hj
      by_cases equal : j = k
      · subst j; exact last
      · rw [drawFrame_bytes Ft (L.outputApart j (by omega) k (by omega) equal) (by have := L.lengthBound; omega)]
        exact prior j (by omega)
    · intro r hr
      exact List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega), hr⟩
end VG.Proof.Dsa.X86.Generation
