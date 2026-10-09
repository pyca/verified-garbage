import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def gatherWord (len : Nat) (second : Bool) (a b : BitVec 128) : BitVec 128 :=
  (if len=2 then (if second then VPermOp.trn2 else .trn1)
    else (if second then .uzp2 else .uzp1)).eval (if len=2 then .d2 else .s4) a b

def scatterWord (len : Nat) (second : Bool) (a b : BitVec 128) : BitVec 128 :=
  (if len=2 then (if second then VPermOp.trn2 else .trn1)
    else (if second then .zip2 else .zip1)).eval (if len=2 then .d2 else .s4) a b

def packedResult (len : Nat) (second : Bool) (a b : BitVec 128) (z : Nat → Int) : BitVec 128 :=
  let x := gatherWord len false a b
  let y := fastVector (gatherWord len true a b) z
  scatterWord len second (VArr.s4.map2 (fun _ a b => a+b) x y)
    (VArr.s4.map2 (fun _ a b => a-b) x y)

/-- Exact packed butterfly, without assuming canonical input representatives. -/
theorem renInnerPair_ok (a b tmp : VReg) (len : Nat)
    (hab : a ≠ b) (ha : a ∉ [.v25,.v26]) (hb : b ∉ [.v25,.v26])
    (hat : a ≠ tmp) (ht : tmp ≠ .v25) (ht26 : tmp ≠ .v26)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e < 4, 0 ≤ z e ∧ z e < 8380417)
    (hzw : ∀ e < 4, vword (s.v .v18) e = BitVec.ofInt 32 (z e))
    (hbw : ∀ e < 4, vword (s.v .v19) e = BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (k : ∀ t, VChg [.v25,.v26,.v4,tmp,a,b] s t →
      t.v a = packedResult len false (s.v a) (s.v b) z →
      t.v b = packedResult len true (s.v a) (s.v b) z → WP isa (.block rest) t Q) :
    WP isa (.block (renInnerPair a b tmp len ++ rest)) s Q := by
  have ha25 : a ≠ .v25 := fun h => ha (by simp [h])
  have hb25 : b ≠ .v25 := fun h => hb (by simp [h])
  simp only [renInnerPair, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_vop (d := .v25) rfl fun s₁ h₁ => wp_vop (d := .v26) rfl fun s₂ h₂ => ?_
  have hu : s₂.v .v25 = gatherWord len false (s.v a) (s.v b) := by
    rw [h₂.get .v25, h₁.v]
    rfl
  have hv : s₂.v .v26 = gatherWord len true (s.v a) (s.v b) := by
    rw [h₂.v,h₁.get a ha25,h₁.get b hb25]
    rfl
  refine fastMul_ok (d := .v26) (tmp := .v4) (zr := .v18) (br := .v19) (qr := .v16)
    (by decide) (by decide) (by decide) (by decide) hz ?_ ?_ ?_ fun s₃ hc₃ hv₃ => ?_
  · simpa only [h₂.get .v18, h₁.get .v18] using hzw
  · simpa only [h₂.get .v19, h₁.get .v19] using hbw
  · simpa only [h₂.get .v16, h₁.get .v16] using hqw
  · have hm : s₃.v .v26 = fastVector (gatherWord len true (s.v a) (s.v b)) z := by
      apply VG.AArch64.vec_ext
      intro e he
      rw [hv₃ e he,hv,fastVector_word _ _ he]
    have hu₃ : s₃.v .v25 = gatherWord len false (s.v a) (s.v b) := by
      rw [hc₃.get .v25,hu]
    refine wp_vop (d := tmp) rfl fun s₄ h₄ => wp_vop (d := .v25) rfl fun s₅ h₅ =>
      wp_vop (d := a) rfl fun s₆ h₆ => wp_vop (d := b) rfl fun s₇ h₇ => ?_
    refine k s₇ (VChg.mono (((((h₁.chg.trans h₂.chg).trans hc₃).trans h₄.chg).trans h₅.chg).trans
      (h₆.chg.trans h₇.chg)) ?_) ?_ ?_
    · intro v hv
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
      grind only
    · rw [h₇.get a hab,h₆.v,h₅.v,h₄.get .v25 (Ne.symm ht),h₄.get .v26 (Ne.symm ht26),
        h₅.get tmp ht,h₄.v,hu₃,hm]
      rfl
    · rw [h₇.v,h₆.get .v25 (Ne.symm ha25),h₆.get tmp (Ne.symm hat),h₅.v,
        h₄.get .v25 (Ne.symm ht),h₄.get .v26 (Ne.symm ht26),h₅.get tmp ht,h₄.v,hu₃,hm]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized
