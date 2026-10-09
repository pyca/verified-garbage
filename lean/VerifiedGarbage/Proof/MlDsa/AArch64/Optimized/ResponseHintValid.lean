import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintNorm
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintPacked

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem hintFailure_false (m : Mem) (B : BitVec 32) (p a h : Addr)
    (hd : (pR p).Disjoint (pR a)) :
    hintFailure m B p a h 64=false ↔ ∀k<256,hintNormTest m a B k := by
  unfold hintFailure
  simp only [Bool.or_eq_false_iff]
  rw [hintLaneFailure_false m B p a h hd (by decide) (by decide),
    hintLaneFailure_false m B p a h hd (by decide) (by decide),
    hintLaneFailure_false m B p a h hd (by decide) (by decide),
    hintLaneFailure_false m B p a h hd (by decide) (by decide)]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ k hk
    have he : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3 := by omega
    rcases he with he | he | he | he
    · simpa only [show 4*(k/4)+0=k by omega] using h0 (k/4) (by omega)
    · simpa only [show 4*(k/4)+1=k by omega] using h1 (k/4) (by omega)
    · simpa only [show 4*(k/4)+2=k by omega] using h2 (k/4) (by omega)
    · simpa only [show 4*(k/4)+3=k by omega] using h3 (k/4) (by omega)
  · intro h
    exact ⟨⟨⟨fun i hi => h _ (by omega),fun i hi => h _ (by omega)⟩,
      fun i hi => h _ (by omega)⟩,fun i hi => h _ (by omega)⟩

theorem hintFailure_field (m : Mem) (B : Nat) (p a h : Addr)
    (hd : (pR p).Disjoint (pR a)) (hB : 1≤B) (hB' : B≤524288)
    (hr : ∀k<256,-8380417<(coeffAt m a k).toInt ∧ (coeffAt m a k).toInt<2*8380417) :
    hintFailure m (BitVec.ofNat 32 B) p a h 64=false ↔
      ∀k<256,normZq (ofInt (coeffAt m a k).toInt)<B := by
  rw [hintFailure_false m _ p a h hd]
  constructor
  · intro hv k hk
    exact (hintNormTest_field hB hB' (hr k hk).1 (hr k hk).2).mp (hv k hk)
  · intro hv k hk
    exact (hintNormTest_field hB hB' (hr k hk).1 (hr k hk).2).mpr (hv k hk)

end VG.Proof.MlDsa.AArch64.Optimized.Response
