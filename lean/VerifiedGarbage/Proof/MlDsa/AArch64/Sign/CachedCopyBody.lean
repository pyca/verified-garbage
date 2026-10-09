import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_ldrx wp_strx wp_addImm wp_subImm wp_nil)

theorem copyBody_ok (s : State)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x1) 8) (hout : InRegions s.wr (s.gpr .x0) 8) :
    WP isa (.block Impl.MlDsa.AArch64.Sign.Cached.copyBody) s fun t=>
      t.mem=s.mem.writeW (s.gpr .x0) (s.mem.readW (s.gpr .x1) 64) ∧
      t.gpr .x0=s.gpr .x0+8 ∧ t.gpr .x1=s.gpr .x1+8 ∧
      t.gpr .x2=s.gpr .x2-BitVec.ofNat 64 1 ∧ Keep [.x0,.x1,.x2,.x9] s t := by
  have e0 : s.gpr .x0+BitVec.ofNat 64 0=s.gpr .x0 := BitVec.add_zero _
  have e1 : s.gpr .x1+BitVec.ofNat 64 0=s.gpr .x1 := BitVec.add_zero _
  refine wp_ldrx (a:=s.gpr .x1) (by decide) e1 hin fun a ha va=>
    wp_strx (a:=s.gpr .x0) (by decide) (by rw [ha.get .x0,e0]) (by rw [ha.wr];exact hout) fun b hb=>
    wp_addImm (by decide) fun c hc vc=>wp_addImm (by decide) fun d hd vd=>
    wp_subImm (by decide) fun t ht vt=>wp_nil ?_
  refine ⟨?_,?_,?_,?_,((((ha.keep.trans hb.keep).trans hc.keep).trans hd.keep).trans ht.keep).mono (by simp)⟩
  · rw [ht.mem,hd.mem,hc.mem,hb.mem,va,ha.mem]
  · rw [ht.get .x0,hd.get .x0,vc,show b.gpr .x0=a.gpr .x0 by rw [hb.gpr],ha.get .x0]
    rfl
  · rw [ht.get .x1,vd,hc.get .x1,show b.gpr .x1=a.gpr .x1 by rw [hb.gpr],ha.get .x1]
    rfl
  · rw [vt,hd.get .x2,hc.get .x2,show b.gpr .x2=a.gpr .x2 by rw [hb.gpr],ha.get .x2]

end VG.Proof.MlDsa.AArch64.Sign.Cached
