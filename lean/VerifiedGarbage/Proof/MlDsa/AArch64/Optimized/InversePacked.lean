import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def gather (len : Nat) (second : Bool) (a b : BitVec 128) : BitVec 128 :=
  (if len=1 then (if second then VPermOp.uzp2 else .uzp1)
    else (if second then .trn2 else .trn1)).eval (if len=1 then .s4 else .d2) a b

def scatter (len : Nat) (second : Bool) (a b : BitVec 128) : BitVec 128 :=
  (if len=1 then (if second then VPermOp.zip2 else .zip1)
    else (if second then .trn2 else .trn1)).eval (if len=1 then .s4 else .d2) a b

def packedResult (len : Nat) (second : Bool) (a b : BitVec 128) (z : Nat → Int) : BitVec 128 :=
  let x := gather len false a b
  let y := gather len true a b
  scatter len second (VArr.s4.map2 (fun _ a b => a+b) x y)
    (fastVector (VArr.s4.map2 (fun _ a b => a-b) x y) z)

/-- Packed inverse layers use exact gather/scatter permutations; their
only field multiplication is on the difference branch. -/
theorem packed_ok (a b : VReg) (len : Nat) (hab : a≠b)
    (ha : a∉[.v16,.v17,.v18]) (hb : b∉[.v16,.v17,.v18])
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v20) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v21) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg [.v16,.v17,.v18,.v19,a,b] s t →
      t.v a=packedResult len false (s.v a) (s.v b) z →
      t.v b=packedResult len true (s.v a) (s.v b) z → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Inverse.packed a b len ++ rest)) s Q := by
  have ha16 : a≠.v16 := fun h => ha (by simp [h])
  have ha18 : a≠.v18 := fun h => ha (by simp [h])
  have hb16 : b≠.v16 := fun h => hb (by simp [h])
  simp only [VG.Impl.MlDsa.AArch64.Optimized.Inverse.packed,
    VG.Impl.MlDsa.AArch64.Optimized.Inverse.mul,List.cons_append,List.nil_append]
  refine wp_vop (d := .v16) rfl fun s₁ h₁ => wp_vop (d := .v17) rfl fun s₂ h₂ =>
    wp_vop (d := .v18) rfl fun s₃ h₃ => wp_vop (d := .v16) rfl fun s₄ h₄ => ?_
  have hx : s₂.v .v16=gather len false (s.v a) (s.v b) := by
    rw [h₂.get .v16,h₁.v]
    rfl
  have hy : s₂.v .v17=gather len true (s.v a) (s.v b) := by
    rw [h₂.v,h₁.get a ha16,h₁.get b hb16]
    rfl
  have hd : s₄.v .v18=VArr.s4.map2 (fun _ a b => a-b)
      (gather len false (s.v a) (s.v b)) (gather len true (s.v a) (s.v b)) := by
    rw [h₄.get .v18,h₃.v,hx,hy]
  have hs : s₄.v .v16=VArr.s4.map2 (fun _ a b => a+b)
      (gather len false (s.v a) (s.v b)) (gather len true (s.v a) (s.v b)) := by
    rw [h₄.v,h₃.get .v16,h₃.get .v17,hx,hy]
  refine fastMul_ok (d := .v18) (tmp := .v19) (zr := .v20) (br := .v21) (qr := .v31)
    (by decide) (by decide) (by decide) (by decide) hz ?_ ?_ ?_ fun s₅ hc hv => ?_
  · simpa only [h₄.get .v20,h₃.get .v20,h₂.get .v20,h₁.get .v20] using hzw
  · simpa only [h₄.get .v21,h₃.get .v21,h₂.get .v21,h₁.get .v21] using hbw
  · simpa only [h₄.get .v31,h₃.get .v31,h₂.get .v31,h₁.get .v31] using hqw
  · have hm : s₅.v .v18=fastVector (s₄.v .v18) z := by
      apply VG.AArch64.vec_ext
      intro e he
      rw [hv e he,fastVector_word _ _ he]
    have hf : s₅.v .v16=s₄.v .v16 := hc.get .v16 (by decide)
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
      · rw [h₇.v,h₆.get .v16 (Ne.symm ha16),h₆.get .v18 (Ne.symm ha18),hf,hm,hd,hs]
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
      · rw [h₇.v,h₆.get .v16 (Ne.symm ha16),h₆.get .v18 (Ne.symm ha18),hf,hm,hd,hs]
        simp [packedResult,scatter,hl]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
