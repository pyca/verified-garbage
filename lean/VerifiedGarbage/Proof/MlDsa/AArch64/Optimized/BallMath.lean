import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.BallLoop

/-! Splitting the sampler byte stream does not change its deterministic fold. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.Sha3 (length_squeezeFrom squeezeFrom_getElem)

theorem signs_append {X : List Byte} (hX : 8≤X.length) (Y : List Byte) :
    signs (X++Y)=signs X := by
  simp only [signs,List.take_append_of_le_length hX]

theorem fold_append_bytes (τ : Nat) {X : List Byte} (hX : 8≤X.length) (Y : List Byte) :
    ballFold τ (X++Y)=bFold τ (signs X) (ballFold τ X) Y := by
  simp only [ballFold,signs_append hX,List.drop_append_of_le_length hX,bFold_append]

theorem fold_append_done {τ : Nat} {X : List Byte} (hX : 8≤X.length)
    (hf : (ballFold τ X).2=256) (Y : List Byte) : ballFold τ (X++Y)=ballFold τ X := by
  rw [fold_append_bytes τ hX,bFold_full hf]

/-- The second call resumes exactly the suffix of the272-byte SHAKE stream. -/
theorem squeeze_split (S : Spec.Sha3.State) :
    Spec.Sha3.squeezeFrom 136 S 0 272 =
      Spec.Sha3.squeezeFrom 136 S 0 136 ++ Spec.Sha3.squeezeFrom 136 S 136 136 := by
  apply List.ext_getElem
  · simp only [List.length_append,length_squeezeFrom (rate := 136) (by decide) (by decide)]
  · intro i hi hi'
    rw [squeezeFrom_getElem (by decide) (by decide) S (by
      rw [length_squeezeFrom (rate := 136) (by decide) (by decide)] at hi; exact hi)]
    by_cases h : i<136
    · rw [List.getElem_append_left (by rw [length_squeezeFrom (rate := 136) (by decide) (by decide)]; exact h),
        squeezeFrom_getElem (by decide) (by decide) S h]
    · rw [List.getElem_append_right (by rw [length_squeezeFrom (rate := 136) (by decide) (by decide)]; omega)]
      simp only [length_squeezeFrom (rate := 136) (by decide) (by decide)]
      rw [squeezeFrom_getElem (by decide) (by decide) S (by
          rw [length_squeezeFrom (rate := 136) (by decide) (by decide)] at hi; omega)]
      rw [show 136+(i-136)=0+i from by omega]
end VG.Proof.MlDsa.AArch64.Optimized.Ball
