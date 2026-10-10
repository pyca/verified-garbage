import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeState

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeLoopStep_ok (sha3 : Bool) {σ s : State} {c : SqueezeCfg}
    {A : Nat→Spec.Sha3.State} {j : Nat} (hl : SqueezeLayout σ c)
    (hi : SqueezeInv σ s c A j) (hj : j<2) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeStep sha3) s fun t=>
      SqueezeInv σ t c A (j+1) := by
  refine WP.mono (squeezeStep_ok sha3 hi.r22 hi.r23 hi.r24 hi.r25 hi.r26 hi.r27
    hi.first hi.second ((hl.left j hj).keep hi.keep.rd hi.keep.wr)
    ((hl.right j hj).keep hi.keep.rd hi.keep.wr)
    (by rw [hi.keep.gpr .x19 (by decide)]; exact hl.base) (hl.apart j hj) (hl.scratch j hj)
    (by rw [hi.keep.wr]; exact hl.callP) (by rw [hi.keep.wr]; exact hl.callQ)) fun t ht=>?_
  have hf : Frame (c.stepWrites j) s.mem t.mem := ht.frame
  refine ⟨by omega,(hi.keep.trans ht.keep).mono (by decide),hi.frame.trans (hf.sub (hl.covers j hj)),
    ht.first,ht.second,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi4
    refine ((hi.streams i hi4).keep hf (fun k hk=>hl.past i hi4 k j hk hj)).succ ?_
    rcases (show i=0∨i=1∨i=2∨i=3 by omega) with rfl|rfl|rfl|rfl
    · exact ht.rateA
    · exact ht.rateB
    · exact ht.rateC
    · exact ht.rateD
  · rw [ht.keep.gpr .x22 (by decide)]; exact hi.r22
  · rw [ht.keep.gpr .x23 (by decide)]; exact hi.r23
  · rw [ht.nextA,c.next]
  · rw [ht.nextB,c.next]
  · rw [ht.nextC,c.next]
  · rw [ht.nextD,c.next]
  · rw [ht.count,hi.count]
    change BitVec.ofNat 64 (2-j)-1#64=_
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (2-j) 1 (by decide) (by omega)]
    congr 1

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
