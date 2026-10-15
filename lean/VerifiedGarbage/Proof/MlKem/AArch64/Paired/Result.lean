module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.SampleLoop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Bounded paired rejection agrees with the public SampleNTT specification -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.Spec.MlKem VG.Proof.MlKem

theorem accepted_seed (m : Mem) (p : Addr) {k : Nat} (hk : 0<k) (hk256 : k≤256)
    (a blocks : Nat) :
    accepted (seedState m p a k) blocks =
      sampleAfter [] (xofByte (seedBytes m p a k)) (56*blocks) := by
  unfold accepted
  exact sampleAfter_congr [] (fun i _ => shakeStream_seed m p hk hk256 a i)

/-- The padded output is the specified polynomial whenever all coefficients were found. -/
theorem coeffs_sample_result {m : Mem} {out : Addr} {B : List Byte}
    (hc : CoeffsUpTo m out (sampleAfter [] (xofByte B) 280).length
      (Sample.cv (sampleAfter [] (xofByte B) 280)) (fun _ => 0)) :
    ((sampleAfter [] (xofByte B) 280).length=256 ∧
      sampleNTT 280 B=some (polyAt m out)) ∨
    ((sampleAfter [] (xofByte B) 280).length≠256 ∧ sampleNTT 280 B=none) := by
  by_cases h : (sampleAfter [] (xofByte B) 280).length=256
  · refine .inl ⟨h, ?_⟩
    rw [sampleNTT_of_full (Nat.le_refl 280) h]
    rw [h] at hc
    exact congrArg some ((CoeffsUpTo.polyIs hc fun _ hi => Sample.cv_toPoly hi).2).symm
  · exact .inr ⟨h,sampleNTT_none h⟩

theorem accepted_result {seedMem m : Mem} {seed out : Addr} {a k : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (hc : CoeffsUpTo m out (accepted (seedState seedMem seed a k) 5).length
      (Sample.cv (accepted (seedState seedMem seed a k) 5)) (fun _ => 0)) :
    ((accepted (seedState seedMem seed a k) 5).length=256 ∧
      sampleNTT 280 (seedBytes seedMem seed a k)=some (polyAt m out)) ∨
    ((accepted (seedState seedMem seed a k) 5).length≠256 ∧
      sampleNTT 280 (seedBytes seedMem seed a k)=none) := by
  rw [accepted_seed seedMem seed hk hk256] at hc ⊢
  exact coeffs_sample_result hc

end VG.Proof.MlKem.AArch64.Paired
