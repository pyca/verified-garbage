import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Sample (rbLoad)

private theorem lowByte : ∀b : Byte,(b.setWidth 64 &&& 15)=BitVec.ofNat 64 (b.toNat%16) := by decide
private theorem highByte : ∀b : Byte,(b.setWidth 64 >>>4)=BitVec.ofNat 64 (b.toNat/16) := by decide

theorem scalarLoad_ok {s : State} (h11 : s.gpr .x11=15)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 1) :
    WP isa (.block rbLoad) s fun t=>Only [.x2,.x5,.x6,.x7] s t ∧
      t.gpr .x2=s.gpr .x2+1 ∧ t.gpr .x5=s.gpr .x5-1 ∧
      t.gpr .x6=(s.mem (s.gpr .x2)).setWidth 64 ∧
      t.gpr .x7=BitVec.ofNat 64 ((s.mem (s.gpr .x2)).toNat%16) := by
  unfold rbLoad
  refine wp_ldrb (by decide) (by simp) hr fun a ha h6=>
    wp_addImm (by decide) fun b hb h2=>wp_subImm (by decide) fun c hc h5=>
    wp_and fun t ht h7=>wp_nil ?_
  refine ⟨(((ha.trans hb).trans hc).trans ht).mono (by decide),?_,?_,?_,?_⟩
  · rw [ht.get .x2,hc.get .x2,h2,ha.get .x2]
    rfl
  · rw [ht.get .x5,h5,hb.get .x5,ha.get .x5]
    rfl
  · rw [ht.get .x6,hc.get .x6,hb.get .x6,h6]
  · rw [h7,hc.get .x6,hb.get .x6,h6,hc.get .x11,hb.get .x11,ha.get .x11,h11]
    exact lowByte _

theorem scalarHigh_ok {s : State} {b : Byte} (h6 : s.gpr .x6=b.setWidth 64) :
    WP isa (.block [.lsr .x .x7 .x6 4]) s fun t=>Only [.x7] s t ∧
      t.gpr .x7=BitVec.ofNat 64 (b.toNat/16) := by
  refine wp_lsr (by decide) fun t ht h7=>wp_nil ⟨ht,?_⟩
  rw [h7,h6]
  exact highByte b

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
