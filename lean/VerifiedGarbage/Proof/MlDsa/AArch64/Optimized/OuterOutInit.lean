import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterOutLoop

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem outerOut_ok {s : State} {z : Nat → Int} (h : HoistedMem s z)
    (hr : ∀ u < 8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x11+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u < 8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa outerOut s fun t => Keep [.x2,.x5,.x11] s t ∧ Hoisted t z ∧
      t.gpr .x2=s.gpr .x0+128 ∧ t.gpr .x11=s.gpr .x11+128 ∧ t.mem=outerOutPassMem s.mem (s.gpr .x0) (s.gpr .x11) z 8 := by
  rw [outerOut_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (outerSetup_ok s) fun s₁ ⟨⟨⟨hp₁,hc₁,hm₁⟩,hk₁⟩,hv₁⟩ => ?_
  have ht₁ : HoistedMem s₁ z := by
    refine ⟨h.range,?_,?_,?_⟩
    · simpa only [hv₁] using h.q
    · simpa only [hk₁.rd,hk₁.wr,hk₁.get .x1] using h.read
    · simpa only [hm₁,hk₁.get .x1] using h.roots
  refine hoistedInit_ok ht₁ (rest := []) fun s₂ hk₂ ht₂ => ?_
  apply WP.block_nil_iff.mpr
  refine WP.mono (outerOutLoop_ok ht₂ ?_ ?_ ?_) fun t ⟨hk₃,ht₃,hp₃,hs₃,hm₃⟩ => ?_
  · simpa only [hk₂.gpr] using hc₁
  · simpa only [hk₂.rd,hk₂.wr,hk₂.gpr,hk₁.rd,hk₁.wr,hk₁.get .x11] using hr
  · simpa only [hk₂.wr,hk₂.gpr,hk₁.wr,hp₁] using hw
  · refine ⟨((hk₁.trans hk₂.keep).trans hk₃).mono,ht₃,?_,?_,?_⟩
    · simpa only [hk₂.gpr,hp₁] using hp₃
    · simpa only [hk₂.gpr,hk₁.get .x11] using hs₃
    · simpa only [hk₂.mem,hm₁,hk₂.gpr,hp₁,hk₁.get .x11] using hm₃

end VG.Proof.MlDsa.AArch64.Optimized
