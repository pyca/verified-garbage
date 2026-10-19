module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.SampleLoop

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
theorem coeffs_sample_result {w16 : Bool} {m : Mem} {out : Addr} {B : List Byte}
    (hc : CoeffsUpToW w16 m out (sampleAfter [] (xofByte B) 280).length
      (Sample.cvW w16 (sampleAfter [] (xofByte B) 280)) (fun _ => 0)) :
    ((sampleAfter [] (xofByte B) 280).length=256 ∧
      sampleNTT 280 B=some (polyAtW (cw w16) m out)) ∨
    ((sampleAfter [] (xofByte B) 280).length≠256 ∧ sampleNTT 280 B=none) := by
  by_cases h : (sampleAfter [] (xofByte B) 280).length=256
  · refine .inl ⟨h, ?_⟩
    rw [sampleNTT_of_full (Nat.le_refl 280) h]
    rw [h] at hc
    exact congrArg some ((CoeffsUpToW.polyIs hc fun _ hi => Sample.cv_toPoly hi).2).symm
  · exact .inr ⟨h,sampleNTT_none h⟩

theorem accepted_result {w16 : Bool} {seedMem m : Mem} {seed out : Addr} {a k : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (hc : CoeffsUpToW w16 m out (accepted (seedState seedMem seed a k) 5).length
      (Sample.cvW w16 (accepted (seedState seedMem seed a k) 5)) (fun _ => 0)) :
    ((accepted (seedState seedMem seed a k) 5).length=256 ∧
      sampleNTT 280 (seedBytes seedMem seed a k)=some (polyAtW (cw w16) m out)) ∨
    ((accepted (seedState seedMem seed a k) 5).length≠256 ∧
      sampleNTT 280 (seedBytes seedMem seed a k)=none) := by
  rw [accepted_seed seedMem seed hk hk256] at hc ⊢
  exact coeffs_sample_result hc

end VG.Proof.MlKem.AArch64.Paired
