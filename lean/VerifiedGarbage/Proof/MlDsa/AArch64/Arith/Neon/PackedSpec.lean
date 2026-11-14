module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Bfly
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt

/-! ### `MlDsa.AArch64.Arith.Neon.PackedLanes`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Spec.MlDsa (Zq)

/-- Coefficient index of the lower butterfly operand in a packed group. -/
def lower (len e : Nat) : Nat := e+len*(e/len)

/-- Butterfly lane holding coefficient `r` of a packed group. -/
def lane (len r : Nat) : Nat := len*(r/(2*len))+r%len

def result (len : Nat) (A B : Nat → Zq) (r : Nat) : Zq :=
  if r%(2*len) < len then A (lane len r) else B (lane len r)

set_option linter.unusedSimpArgs false

theorem gather_ok {s : State} (len : Nat) (hlen : len = 1 ∨ len = 2) {F : Nat → Zq}
    (h6 : Coeffs (s.v .v6) F) (h7 : Coeffs (s.v .v7) (fun e => F (4+e))) :
    WP isa (.block (gather len)) s fun s' => VChg [.v0,.v1] s s' ∧
      Coeffs (s'.v .v0) (fun e => F (lower len e)) ∧
      Coeffs (s'.v .v1) (fun e => F (lower len e+len)) := by
  rcases hlen with rfl | rfl
  · change WP isa (.block [.vop (.perm .uzp1 .s4 .v0 .v6 .v7),.vop (.perm .uzp2 .s4 .v1 .v6 .v7)]) s _
    refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v0,h₁.v,VG.Proof.MlKem.AArch64.vword_uzp1_s4 _ _ he]
      split
      · rw [h6 _ (by omega_arith)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega_using [])
      · rw [h7 _ (by omega_using [he])]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega_arith)
    · intro e he
      rw [h₂.v,h₁.get .v6,h₁.get .v7,VG.Proof.MlKem.AArch64.vword_uzp2_s4 _ _ he]
      split
      · rw [h6 _ (by omega_arith)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega_using [])
      · rw [h7 _ (by omega_using [he])]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega_arith)
  · change WP isa (.block [.vop (.perm .trn1 .d2 .v0 .v6 .v7),.vop (.perm .trn2 .d2 .v1 .v6 .v7)]) s _
    refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v0,h₁.v,VG.Proof.MlKem.AArch64.vword_trn1_d2 _ _ he]
      split
      · rw [h6 _ (by omega_using [he])]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega_arith)
      · rw [h7 _ (by omega_using [he])]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega_arith)
    · intro e he
      rw [h₂.v,h₁.get .v6,h₁.get .v7,VG.Proof.MlKem.AArch64.vword_trn2_d2 _ _ he]
      split
      · rw [h6 _ (by omega_arith)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega_arith)
      · rw [h7 _ (by omega_using [he])]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega_arith)

theorem scatter_ok {s : State} (len : Nat) (hlen : len = 1 ∨ len = 2) {A B : Nat → Zq}
    (ha : Coeffs (s.v .v0) A) (hb : Coeffs (s.v .v5) B) :
    WP isa (.block (scatter len)) s fun s' => VChg [.v6,.v7] s s' ∧
      Coeffs (s'.v .v6) (result len A B) ∧
      Coeffs (s'.v .v7) (fun e => result len A B (4+e)) := by
  rcases hlen with rfl | rfl
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v6 .v0 .v5),.vop (.perm .zip2 .s4 .v7 .v0 .v5)]) s _
    refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v6,h₁.v,VG.Proof.MlKem.AArch64.vword_zip1_s4' _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega_using [he])]; simp [result,lane,Nat.mod_one,h]
      · rw [hb _ (by omega_using [he])]; simp [result,lane,Nat.mod_one,h,show ¬ e%2 < 1 by omega_using [h]]
    · intro e he
      rw [h₂.v,h₁.get .v0,h₁.get .v5,VG.Proof.MlKem.AArch64.vword_zip2_s4 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega_using [he])]; simp [result,lane,Nat.mod_one,show (4+e)%2 < 1 by omega_using [h],show (4+e)/2 = 2+e/2 by omega_using []]
      · rw [hb _ (by omega_using [he])]; simp [result,lane,Nat.mod_one,show ¬ (4+e)%2 < 1 by omega_using [h],show (4+e)/2 = 2+e/2 by omega_using []]
  · change WP isa (.block [.vop (.perm .trn1 .d2 .v6 .v0 .v5),.vop (.perm .trn2 .d2 .v7 .v0 .v5)]) s _
    refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v6,h₁.v,VG.Proof.MlKem.AArch64.vword_trn1_d2 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega_using [he])]; simp [result,lane,Nat.mod_one,show e%4 < 2 by omega_using [h],show e/4 = 0 by omega_using [he],show e%2 = e by omega_using [h]]
      · rw [hb _ (by omega_using [he])]; simp [result,lane,Nat.mod_one,show ¬ e%4 < 2 by omega_using [he, h],show e/4 = 0 by omega_using [he],show e%2 = e-2 by omega_using [he, h]]
    · intro e he
      rw [h₂.v,h₁.get .v0,h₁.get .v5,VG.Proof.MlKem.AArch64.vword_trn2_d2 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega_using [h])]; simp [result,lane,Nat.mod_one,show (4+e)%4 < 2 by omega_using [h],show e%4 < 2 by omega_using [h],show (4+e)/4 = 1 by omega_using [he],show (4+e)%2 = e by omega_using [h]]
        exact congrArg (fun i => (A i).val) (by omega_using [])
      · rw [hb _ (by omega_using [he])]; simp [result,lane,Nat.mod_one,show ¬ (4+e)%4 < 2 by omega_using [he, h],show ¬ e%4 < 2 by omega_using [he, h],show (4+e)/4 = 1 by omega_using [he],show 2+(4+e)%2 = e by omega_using [he, h]]
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Spec.MlDsa (Poly Zq zetas)
open VG.Proof.MlDsa.Arith
set_option linter.unusedSimpArgs false

/-- A packed batch reads only coefficients not visited by earlier batches. -/
theorem packed_input {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op)
    (F : Poly) (zi : Nat → Nat) (len : Nat) (hlen : len = 1 ∨ len = 2)
    {u r : Nat} (hu : u < 32) (hr : r < 8) :
    (layF blk F len zi ((4/len)*u))[8*u+r]! = F[8*u+r]! := by
  rcases hlen with rfl | rfl
  · rw [layF1_get hblk F zi (by omega_using [hu]) (by omega_using [hu, hr])]
    simp only [Nat.div_one]; rw [ite_eq_right (by omega_using [])]
  · rw [layF2_get hblk F zi (by omega_using [hu]) (by omega_using [hu, hr])]
    simp only [Nat.reduceDiv]; rw [ite_eq_right (by omega_using [])]

/-- Lane indices and coefficient indices agree for both packed layer sizes. -/
theorem packed_indices (len : Nat) (hlen : len = 1 ∨ len = 2) (u r : Nat) :
    lower len (lane len r) = r-r%(2*len)+r%len ∧
    (4/len)*u + lane len r/len = (8*u+r)/(2*len) := by
  rcases hlen with rfl | rfl <;> simp only [lower,lane,Nat.div_one,Nat.mod_one,
    Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul,Nat.reduceDiv] <;> omega_using []

/-- One packed batch has the same result as its corresponding scalar blocks. -/
theorem packed_batch_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op)
    (F : Poly) (zi : Nat → Nat) (len : Nat) (hlen : len = 1 ∨ len = 2)
    {u j : Nat} (hu : u < 32) (hj : j < 256) :
    let G := layF blk F len zi ((4/len)*u)
    let A := fun e => (op G[8*u+lower len e]! G[8*u+lower len e+len]!
      (zetas (zi ((4/len)*u+e/len)))).1
    let B := fun e => (op G[8*u+lower len e]! G[8*u+lower len e+len]!
      (zetas (zi ((4/len)*u+e/len)))).2
    (layF blk F len zi ((4/len)*(u+1)))[j]! =
      if 8*u ≤ j ∧ j < 8*u+8 then result len A B (j-8*u) else G[j]! := by
  dsimp only
  by_cases hin : 8*u ≤ j ∧ j < 8*u+8
  · rw [ite_eq_left hin]
    have hr : j-8*u < 8 := by omega_using [hin]
    have hi := packed_indices len hlen u (j-8*u)
    have hlow : lower len (lane len (j-8*u)) < 8 := by
      rcases hlen with rfl | rfl <;> simp only [lower,lane,Nat.div_one,Nat.mod_one,
        Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul] <;> omega_using [hin]
    have hhigh : lower len (lane len (j-8*u))+len < 8 := by
      rcases hlen with rfl | rfl <;> simp only [lower,lane,Nat.div_one,Nat.mod_one,
        Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul] <;> omega_using [hin]
    unfold result
    dsimp only
    rw [packed_input hblk F zi len hlen hu hlow]
    rw [show 8*u+lower len (lane len (j-8*u))+len =
      8*u+(lower len (lane len (j-8*u))+len) by omega_using [],
      packed_input hblk F zi len hlen hu hhigh]
    have hz : (4/len)*u+lane len (j-8*u)/len = j/(2*len) := by
      rw [hi.2,show 8*u+(j-8*u) = j by omega_using [hin]]
    rw [hz]
    simp only [← Nat.add_assoc]
    rcases hlen with rfl | rfl
    · rw [layF1_get hblk F zi (by omega_using [hu]) hj,ite_eq_left (by omega_using [hin])]
      by_cases he : j%2 = 0
      · simp only [ite_eq_left he]
        rw [ite_eq_left (by omega_using [he]),show 8*u+lower 1 (lane 1 (j-8*u)) = j by
          simp only [lower,lane,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul]; omega_using [hin, he]]
      · simp only [ite_eq_right he]
        rw [ite_eq_right (by omega_using [hin, he]),show 8*u+lower 1 (lane 1 (j-8*u)) = j-1 by
          simp only [lower,lane,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul]; omega_using [hin, he]]
        simp only [Nat.reduceMul]
        rw [show j-1+1 = j by omega_using [he]]
    · rw [layF2_get hblk F zi (by omega_using [hu]) hj,ite_eq_left (by omega_using [hin])]
      by_cases he : j%4 < 2
      · simp only [ite_eq_left he]
        rw [ite_eq_left (by omega_using [he]),show 8*u+lower 2 (lane 2 (j-8*u)) = j by
          simp only [lower,lane,Nat.reduceMul]; omega_using [hin, he]]
      · simp only [ite_eq_right he]
        rw [ite_eq_right (by omega_using [hin, he]),show 8*u+lower 2 (lane 2 (j-8*u)) = j-2 by
          simp only [lower,lane,Nat.reduceMul]; omega_using [hin, he]]
        simp only [Nat.reduceMul]
        rw [show j-2+2 = j by omega_using [he]]
  · rw [ite_eq_right hin]
    rcases hlen with rfl | rfl
    · rw [layF1_get hblk F zi (by omega_using [hu]) hj,layF1_get hblk F zi (by omega_using [hu]) hj]
      simp only [Nat.div_one]
      by_cases h : j < 8*u <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · rw [layF2_get hblk F zi (by omega_using [hu]) hj,layF2_get hblk F zi (by omega_using [hu]) hj]
      simp only [Nat.reduceDiv]
      by_cases h : j < 8*u <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]

end VG.Proof.MlDsa.AArch64.Arith.Neon
