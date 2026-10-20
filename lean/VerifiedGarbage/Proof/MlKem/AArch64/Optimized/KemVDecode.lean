module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVInv

/-! # Decode the public vector after the matrix has been consumed -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

theorem firstRow_vfar {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) :
    VFar P L s₀ kC co P.k P.k (R (kA s₀) L.sc AH (1024*P.k)) := by
  have hw := hp.wf
  have hkk := Nat.mul_le_mul_right P.k hw.facts.1
  simp only [Nat.one_mul] at hkk
  have fit : AH+1024*P.k≤SV P+48 := by lom
  refine ⟨sdisj hp (by lom) fit (.inl (by lom)),sdisj hp (by lom) fit (.inl (by lom)),
    sdisj hp (by lom) fit (.inr (by lom)),?_,?_⟩
  · have fc : co+32*P.du*P.k≤L.len (L.slot kC) := by
      have := A.fC; have := Nat.mul_assoc 32 P.du P.k; lom
    refine hp.args.rdisj (hp.lt A.hkC) hp.scb fc (hp.fs fit) (.inr (.inr hp.scw)) ?_
    rcases A.sC with hh | hh
    · exact .inl hh
    · exact .inr (.inr (by rw [hh]; lom))
  · exact ⟨R (kA s₀) L.sc PB (SV P-PB),by simp [encW],R.sub2 (by lom) (by lom)⟩

end VG.Proof.MlKem.AArch64.Kem
