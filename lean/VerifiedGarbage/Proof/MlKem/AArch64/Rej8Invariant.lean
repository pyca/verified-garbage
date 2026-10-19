module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps

/-! # Vector-batch preservation of the scalar rejection invariant -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem sampleAfter_add (L : List Zq) (B : Nat → Byte) (t k : Nat) :
    sampleAfter (sampleAfter L B t) (fun i => B (3*t+i)) k=sampleAfter L B (t+k) := by
  induction k with
  | zero => simp only [sampleAfter_zero,Nat.add_zero]
  | succ k ih =>
    rw [sampleAfter_succ,ih,show t+(k+1)=(t+k)+1 by omega,sampleAfter_succ]
    congr 1 <;> congr 1 <;> omega

theorem batch_frameW (w16 : Bool) (s : State) {aP : Addr} {L : List Zq}
    (h3 : s.gpr .x3=cAddr w16 aP L.length) (hroom : L.length+8≤256) :
    Frame [polyRegion aP] s.mem (updatedMem s w16) := by
  cases w16
  · unfold updatedMem
    rw [ite_eq_right Bool.false_ne_true]
    apply Frame.write (r := polyRegion aP) (Frame.write (r := polyRegion aP) (Frame.refl _ _) (by simp) _ ?_) (by simp) _ ?_
    · rw [h3]
      exact contains_off (by simp only [cs_eq, Bool.false_eq_true, ite_false]; omega) (by decide)
    · rw [h3]
      change (polyRegion aP).Contains (aP+BitVec.ofNat 64 (4*L.length)+BitVec.ofNat 64 16) 16
      rw [ptr_add]
      exact contains_off (by omega) (by decide)
  · unfold updatedMem
    rw [ite_eq_left rfl]
    refine Frame.write (r := polyRegion aP) (Frame.refl _ _) (by simp) _ ?_
    rw [h3]
    exact contains_off (by simp only [cs_eq, ite_true]; omega) (by decide)

theorem batch_invW {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte}
    {bP aP : Addr} {s₀ s u : State} (h : Scalar.InvW w16 initial N B bP aP s₀ t s)
    (hroom : (Scalar.LA initial B t).length+8≤256)
    (hz : ∀i<8,vhalf (s.v .v21) i=0)
    (hb : ∀i<12,s.mem (s.gpr .x2+BitVec.ofNat 64 i)=B (3*t+i))
    (hp : BatchPostW w16 s u) : Scalar.InvW w16 initial N B bP aP s₀ (t+4) u := by
  have he : Scalar.LA initial B t++acceptedValues s=Scalar.LA initial B (t+4) := by
    rw [batch_steps s _ hroom,sampleAfter_congr _ hb,sampleAfter_add]
  have hlen : (Scalar.LA initial B (t+4)).length=
      (Scalar.LA initial B t).length+acceptedCount s := by
    rw [←he,List.length_append,acceptedValues_length]
  have hcount : acceptedCount s≤8 := accepted_length _
  refine ⟨⟨hp.keep.rd.trans h.acc.rd,hp.keep.wr.trans h.acc.wr,hp.keep.sp.trans h.acc.sp,
    by omega,?_,?_,?_,?_,?_,⟩,(h.keep.trans hp.keep).mono (by decide),?_,?_,?_⟩
  · rw [hp.output,h.acc.x3,cAddr_add,hlen]
  · rw [hp.remain,h.acc.x4,hlen]
    omega
  · rw [hp.keep.get .x9,h.acc.x9]
  · rw [hp.mem,←he]
    exact batch_prefixW w16 s h.acc.x3 hroom hz h.acc.coeffs
  · rw [hp.mem]
    exact h.acc.frame.trans (batch_frameW w16 s h.acc.x3 hroom)
  · rw [hp.input,h.x2]
    change bP+BitVec.ofNat 64 (3*t)+BitVec.ofNat 64 12=_
    rw [ptr_add]
    congr 2
  · rw [hp.chunks,h.x5]
    omega
  · rw [hp.keep.get .x10,h.x10]

end VG.Proof.MlKem.AArch64.Rej8
