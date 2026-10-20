module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarLoop

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseAddress
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

theorem parse_ok {s : State} {η : Nat} (he : η=2∨η=4)
    {table p q a : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256) (hx : X.length=272)
    (hv : Layout s table p q X) (hs : ScalarLayout s p q X)
    (hT : TableAt s.mem table) (hS : Stored s.mem p L)
    (hq : s.gpr .x24=q) (hp : s.gpr .x25=p) (ha : s.gpr .x26=a)
    (ht : s.gpr .x19+6000=table)
    (hc : s.mem.readW a 64=BitVec.ofNat 64 (256-L.length))
    (hr : InRegions (s.rd++s.wr) a 8) (hw : InRegions s.wr a 8)
    (hsep : (polyR p).Disjoint ⟨a,8⟩) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η) s fun t=>
      Keep batchRegs s t ∧ Frame [polyR p,⟨a,8⟩] s.mem t.mem ∧
      Stored t.mem p (rbFold η L X) ∧
      t.mem.readW a 64=BitVec.ofNat 64 (256-(rbFold η L X).length) ∧
      t.gpr .x24=q+BitVec.ofNat 64 544 ∧ t.gpr .x25=p+BitVec.ofNat 64 1024 ∧
      t.gpr .x26=a+BitVec.ofNat 64 8 ∧ t.gpr .x27=s.gpr .x27-BitVec.ofNat 64 1 := by
  rw [parse_wp]
  refine WP.seq (WP.mono (parseAddress_ok (by rw [ha]; exact hr)) fun u ⟨hu,h2,h3,h4⟩=>?_)
  rw [hq] at h2
  rw [hp] at h3
  rw [ha,hc] at h4
  refine WP.seq (WP.mono (parseCore_ok he hl hx (hv.keep hu.keep hu.mem)
    (hs.keep hu.keep hu.mem) (by rw [hu.mem]; exact hT)
    (by rw [hu.mem]; exact hS) h2 h3 h4
    (by rw [hu.get .x19]; exact ht)) fun v ⟨hvK,hvF,hvS,hvC⟩=>?_)
  have hvA : v.gpr .x26+BitVec.ofNat 64 0=a := by
    rw [hvK.gpr .x26 (by decide),hu.get .x26,ha]; exact BitVec.add_zero _
  unfold VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parseNext
  refine wp_strx (by decide) hvA (by rw [hvK.wr,hu.wr]; exact hw) fun w htw=>
    wp_addImm (by decide) fun x hx2 ex => wp_addImm (by decide) fun y hy ey =>
    wp_addImm (by decide) fun z hz ez => wp_subImm (by decide) fun t ht et => wp_nil ?_
  have hm : t.mem=w.mem := by rw [ht.mem,hz.mem,hy.mem,hx2.mem]
  have hf : Frame [⟨a,8⟩] v.mem t.mem := by
    rw [hm,htw.mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self a 8)
  refine ⟨(((((hu.keep.trans hvK).trans htw.keep).trans hx2.keep).trans hy.keep).trans
    hz.keep |>.trans ht.keep).mono (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · have hfull : Frame [polyR p,⟨a,8⟩] u.mem t.mem := (hvF.mono (fun r hr=>by simp only [List.mem_singleton] at hr; simp [hr])).trans
      (hf.mono (fun r hr=>by simp only [List.mem_singleton] at hr; simp [hr]))
    rw [hu.mem] at hfull
    exact hfull
  · exact stored_frame hf (fun r hr=>by rw [List.mem_singleton.mp hr]; exact hsep)
      hvS (rbFold_length_le hl _)
  · rw [hm,htw.mem,Mem.readW_writeW_self64]
    rw [←hvC]
    simp
  · rw [ht.get .x24,hz.get .x24,hy.get .x24,ex,htw.gpr,hvK.gpr .x24 (by decide),hu.get .x24,hq]
  · rw [ht.get .x25,hz.get .x25,ey,hx2.get .x25,htw.gpr,hvK.gpr .x25 (by decide),hu.get .x25,hp]
  · rw [ht.get .x26,ez,hy.get .x26,hx2.get .x26,htw.gpr,hvK.gpr .x26 (by decide),hu.get .x26,ha]
  · rw [et,hz.get .x27,hy.get .x27,hx2.get .x27,htw.gpr,hvK.gpr .x27 (by decide),hu.get .x27]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
