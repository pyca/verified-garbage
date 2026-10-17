module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVTail
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Lists

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


theorem v_decode {s₀ s : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (ht : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (h : VInv P L s₀ kC co mE mB v rv mv P.k P.k s) :
    WPs ((List.range P.k).map fun j => dec12At (slotReg kE) (eo+384*j) (aOff P 0 j)) s fun t =>
      VInv P L s₀ kC co mE mB v rv mv P.k P.k t ∧
      DecodeInv P L s₀ s.mem T (encY rv) v P.k t := by
  have hd : DecodeInv P L s₀ s.mem T (encY rv) v 0 s :=
    ⟨h.kb,h.x24,fun _ hj => by omega,h.y,Frame.refl _ _⟩
  exact WPs.mono (decode_all hp A.hkE A.rE A.fE ht hd) fun t dt =>
    ⟨h.frame hp dt.kb (dt.x24.trans h.x24.symm) dt.frame (fun r hh => by
      rw [List.mem_singleton.mp hh]; exact firstRow_vfar hp A),dt⟩

end VG.Proof.MlKem.AArch64.Kem
