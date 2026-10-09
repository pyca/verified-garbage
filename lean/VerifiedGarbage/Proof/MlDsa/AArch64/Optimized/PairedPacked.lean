import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePacked

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (gather scatter packedResult)

/-- Packed inverse layers use exact gather/scatter permutations; their
only field multiplication is on the difference branch. -/
theorem packed_ok (a b : VReg) (len : Nat) (hab : a≠b)
    (ha : a∉[.v24,.v25,.v26]) (hb : b∉[.v24,.v25,.v26])
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg [.v24,.v25,.v26,.v27,a,b] s t →
      t.v a=packedResult len false (s.v a) (s.v b) z →
      t.v b=packedResult len true (s.v a) (s.v b) z → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed a b len ++ rest)) s Q := by
  have ha16 : a≠.v24 := fun h => ha (by simp [h])
  have ha18 : a≠.v26 := fun h => ha (by simp [h])
  have hb16 : b≠.v24 := fun h => hb (by simp [h])
  simp only [VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed,
    List.cons_append,List.nil_append]
  refine wp_vop (d := .v24) rfl fun s₁ h₁ => wp_vop (d := .v25) rfl fun s₂ h₂ =>
    wp_vop (d := .v26) rfl fun s₃ h₃ => wp_vop (d := .v24) rfl fun s₄ h₄ => ?_
  have hx : s₂.v .v24=gather len false (s.v a) (s.v b) := by
    rw [h₂.get .v24,h₁.v]
    rfl
  have hy : s₂.v .v25=gather len true (s.v a) (s.v b) := by
    rw [h₂.v,h₁.get a ha16,h₁.get b hb16]
    rfl
  have hd : s₄.v .v26=VArr.s4.map2 (fun _ a b => a-b)
      (gather len false (s.v a) (s.v b)) (gather len true (s.v a) (s.v b)) := by
    rw [h₄.get .v26,h₃.v,hx,hy]
  have hs : s₄.v .v24=VArr.s4.map2 (fun _ a b => a+b)
      (gather len false (s.v a) (s.v b)) (gather len true (s.v a) (s.v b)) := by
    rw [h₄.v,h₃.get .v24,h₃.get .v25,hx,hy]
  refine fastMul_ok (d := .v26) (tmp := .v27) (zr := .v28) (br := .v29) (qr := .v31)
    (by decide) (by decide) (by decide) (by decide) hz ?_ ?_ ?_ fun s₅ hc hv => ?_
  · simpa only [h₄.get .v28,h₃.get .v28,h₂.get .v28,h₁.get .v28] using hzw
  · simpa only [h₄.get .v29,h₃.get .v29,h₂.get .v29,h₁.get .v29] using hbw
  · simpa only [h₄.get .v31,h₃.get .v31,h₂.get .v31,h₁.get .v31] using hqw
  · have hm : s₅.v .v26=fastVector (s₄.v .v26) z := by
      apply VG.AArch64.vec_ext
      intro e he
      rw [hv e he,fastVector_word _ _ he]
    have hf : s₅.v .v24=s₄.v .v24 := hc.get .v24 (by decide)
    by_cases hl : len=1
    · simp only [hl,ite_true]
      refine wp_vop (d := a) rfl fun s₆ h₆ => wp_vop (d := b) rfl fun t h₇ => ?_
      refine k t (VChg.mono (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans hc).trans
        (h₆.chg.trans h₇.chg)) ?_) ?_ ?_
      · intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only
      · rw [h₇.get a hab,h₆.v,hf,hm,hd,hs]
        simp [packedResult,scatter,hl]
      · rw [h₇.v,h₆.get .v24 (Ne.symm ha16),h₆.get .v26 (Ne.symm ha18),hf,hm,hd,hs]
        simp [packedResult,scatter,hl]
    · simp only [hl,ite_false]
      refine wp_vop (d := a) rfl fun s₆ h₆ => wp_vop (d := b) rfl fun t h₇ => ?_
      refine k t (VChg.mono (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans hc).trans
        (h₆.chg.trans h₇.chg)) ?_) ?_ ?_
      · intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only
      · rw [h₇.get a hab,h₆.v,hf,hm,hd,hs]
        simp [packedResult,scatter,hl]
      · rw [h₇.v,h₆.get .v24 (Ne.symm ha16),h₆.get .v26 (Ne.symm ha18),hf,hm,hd,hs]
        simp [packedResult,scatter,hl]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
