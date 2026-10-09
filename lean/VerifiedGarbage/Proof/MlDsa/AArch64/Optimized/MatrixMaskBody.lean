import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMaskGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskStep

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (maskRun)

theorem groups_ok {s : State}
    (hr : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 4).flatMap group)) s fun t =>
      StepKeep [.v1] s t ∧ t.mem=maskRun s.mem (s.gpr .x1) (s.v .v0) 4 := by
  refine wp_range_flatMap (M := isa) (N := 4)
    (fun j t => StepKeep [.v1] s t ∧ t.mem=maskRun s.mem (s.gpr .x1) (s.v .v0) j)
    (fun j t hj ht => ?_) 4 (by omega) s ⟨⟨Keep.refl [] s,fun _ _ => rfl⟩,rfl⟩
  refine WP.mono (group_ok hj (by rw [ht.1.keep.rd,ht.1.keep.wr,ht.1.keep.get .x1]; exact hr j hj)
    (by rw [ht.1.keep.wr,ht.1.keep.get .x1]; exact hw j hj)) fun u ⟨hu,hm⟩ => ?_
  refine ⟨(ht.1.trans hu).mono (by decide),?_⟩
  rw [hm,ht.2,ht.1.keep.get .x1,ht.1.vec .v0 (by decide)]
  rfl

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    ((t.gpr .x1=s.gpr .x1+64 ∧ t.gpr .x2=s.gpr .x2-1 ∧ t.mem=s.mem) ∧
      Keep [.x1,.x2] s t) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advance
  arun
  exact ⟨rfl,rfl⟩

theorem body_ok {s : State}
    (hr : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block body) s fun t => Keep [.x1,.x2] s t ∧
      (∀r,r≠.v1→t.v r=s.v r) ∧ t.mem=maskRun s.mem (s.gpr .x1) (s.v .v0) 4 ∧
      t.gpr .x1=s.gpr .x1+64 ∧ t.gpr .x2=s.gpr .x2-1 := by
  rw [body,WP.block_append_iff]
  refine WP.mono (groups_ok hr hw) fun a ⟨ha,hm⟩ => ?_
  refine WP.mono (advance_ok a) fun t ⟨⟨⟨hp,hc,hmem⟩,hk⟩,hv⟩ => ?_
  exact ⟨(ha.keep.trans hk).mono (by decide),fun r hn => by
    rw [hv,ha.vec r (by simpa using hn)],hmem.trans hm,
    by rw [hp,ha.keep.get .x1],by rw [hc,ha.keep.get .x2]⟩

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
