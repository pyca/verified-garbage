import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Dot
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotWord

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Impl.MlDsa.AArch64.Optimized

def dotMont (d : VReg) : List Instr := (dotReduce d).take 5

theorem dotMont_ok {d : VReg} {s : State} {rest : List Instr} {Q : State → Prop}
    (p : Nat → BitVec 64)
    (a₁ : s.v .v18=ofVDwords (p 0) (p 1)) (a₂ : s.v .v19=ofVDwords (p 2) (p 3))
    (hq : s.v .v31=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v30=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ t,VChg [.v18,.v19,.v20,d] s t →
      t.v d=ofVWords (redc (p 0)) (redc (p 1)) (redc (p 2)) (redc (p 3)) →
      WP isa (.block rest) t Q) : WP isa (.block (dotMont d++rest)) s Q := by
  have eq_q : (BitVec.ofNat 32 q).setWidth 64=BitVec.ofNat 64 q := by decide
  refine wp_vop (d := .v20) rfl fun s₃ h₃ => ?_
  have a₃ : s₃.v .v20 = ofVWords ((p 0).extractLsb' 0 32) ((p 1).extractLsb' 0 32)
      ((p 2).extractLsb' 0 32) ((p 3).extractLsb' 0 32) := by
    rw [h₃.v, a₁, a₂]; exact unzip_wide false _ _ _ _
  refine wp_vop (d := .v20) rfl fun s₄ h₄ => ?_
  have a₄ : s₄.v .v20 = ofVWords (multiplier (p 0)) (multiplier (p 1))
      (multiplier (p 2)) (multiplier (p 3)) := by
    rw [h₄.v, a₃, h₃.get .v30, hqi, map2_words]
    rfl
  refine wp_vop (d := .v18) rfl fun s₅ h₅ => ?_
  have a₅ : s₅.v .v18 = ofVDwords
      (p 0 + (multiplier (p 0)).setWidth 64 * BitVec.ofNat 64 q)
      (p 1 + (multiplier (p 1)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₅.v, h₄.get .v18, h₃.get .v18, a₁, a₄,
      h₄.get .v31, h₃.get .v31, hq]
    simp only [ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_0,
      vword_ofVWords_1, eq_q]
  refine wp_vop (d := .v19) rfl fun s₆ h₆ => ?_
  have a₆ : s₆.v .v19 = ofVDwords
      (p 2 + (multiplier (p 2)).setWidth 64 * BitVec.ofNat 64 q)
      (p 3 + (multiplier (p 3)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₆.v, h₅.get .v19, h₄.get .v19, h₃.get .v19, a₂, h₅.get .v20, a₄,
      h₅.get .v31, h₄.get .v31, h₃.get .v31, hq]
    simp only [ite_true, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_2,
      vword_ofVWords_3, eq_q]
  refine wp_vop (d := d) rfl fun s₇ h₇ => k s₇
    (VChg.mono (rs' := [.v18,.v19,.v20,d])
      ((((h₃.chg.trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg)
      (by intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_
  rw [h₇.v, h₆.get .v18, a₅, a₆]
  exact unzip_wide true _ _ _ _


theorem dotReduce_ok {d : VReg} (hd : d≠.v31) {s : State} {rest : List Instr} {Q : State → Prop}
    (p : Nat → BitVec 64)
    (a₁ : s.v .v18=ofVDwords (p 0) (p 1)) (a₂ : s.v .v19=ofVDwords (p 2) (p 3))
    (hq : s.v .v31=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v30=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ t,VChg [.v18,.v19,.v20,d] s t →
      (∀e<4,vword (t.v d) e=redc (p e)-BitVec.ofNat 32 q) →
      WP isa (.block rest) t Q) : WP isa (.block (dotReduce d++rest)) s Q := by
  change WP isa (.block (dotMont d++(.vop (.sub .s4 d d .v31)::rest))) s Q
  refine dotMont_ok p a₁ a₂ hq hqi fun t ht hv => ?_
  refine wp_vop (d:=d) rfl fun u hu => ?_
  refine k u ((ht.trans hu.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [hu.v,VG.AArch64.vword_map2 _ _ _ he,ht.get .v31 (by simp [Ne.symm hd]),hv,hq]
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3]

end VG.Proof.MlDsa.AArch64.Optimized
