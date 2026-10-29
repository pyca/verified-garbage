module
public import VerifiedGarbage.Impl.MlKem.AArch64.Dot
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Reduce
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! Reduction of three fused accumulators, before the output interleave. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Impl.MlKem.AArch64

def finish : List Instr :=
  [.vop (.sqdmulh .v24 .v22 .v17), .vop (.mls .v22 .v24 .v16),
   .vop (.mla .v21 .v22 .v18)] ++
  Impl.MlKem.AArch64.Dot.dotReduce .v21 ++ Impl.MlKem.AArch64.Dot.dotReduce .v23

theorem finish_ok {rest : List Instr} {s : State} {Q : State → Prop}
    (hc : VConsts s) {A B C G : Nat → Nat}
    (ha : Lanes (s.v .v21) A) (hb : Lanes (s.v .v22) B)
    (hc' : Lanes (s.v .v23) C) (hg : Lanes (s.v .v18) G)
    (ba : ∀ e < 4, A e ≤ 4 * 3329 * 3329)
    (bb : ∀ e < 4, B e ≤ 4 * 3329 * 3329)
    (bc : ∀ e < 4, C e ≤ 8 * 3329 * 3329)
    (bg : ∀ e < 4, G e < 3329)
    (k : ∀ s', VChg [.v21, .v22, .v23, .v24] s s' →
      Lanes (s'.v .v21) (fun e => (A e + B e * G e) % 3329) →
      Lanes (s'.v .v23) (fun e => C e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (finish ++ rest)) s Q := by
  simp only [finish, List.append_assoc, List.cons_append, List.nil_append]
  refine vbar_ok (d := .v22) (t := .v24) (hc := hc) (hf := hb)
    (hlt := fun e he => by have := bb e he; omega) (k := fun s₁ h₁ l₁ b₁ => ?_)
  have a₁ : Lanes (s₁.v .v21) A := by rw [h₁.get .v21]; exact ha
  have g₁ : Lanes (s₁.v .v18) G := by rw [h₁.get .v18]; exact hg
  let R := fun e => B e - B e * 645083 / 2 ^ 31 * 3329
  try rewrite [show fun e => B e - B e * 645083 / 2 ^ 31 * 3329 = R from rfl] at *
  have br : ∀ e < 4, R e * G e ≤ 2 * 3329 * 3329 := fun e he =>
    Nat.mul_le_mul (Nat.le_of_lt (b₁ e he).1) (Nat.le_of_lt (bg e he))
  have bylt : ∀ e < 4, A e + R e * G e < 2 ^ 31 := fun e he => by
    have := ba e he; have := br e he; omega
  refine wp_vop (d := .v21) rfl fun s₂ h₂ => ?_
  have l₂ : Lanes (s₂.v .v21) (fun e => A e + R e * G e) := by
    rw [h₂.v]
    exact (lanes_mla a₁ l₁ g₁).congr fun e he => by
      have := bylt e he
      rw [Nat.mod_eq_of_lt (show R e * G e < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt (show A e + R e * G e < 2 ^ 32 by omega)]
  have c₂ := (hc.chg h₁).chg h₂.chg
  refine reduce_ok (d := .v21) (by decide) (by decide) (by decide) c₂ l₂ bylt
    fun s₃ h₃ l₃ => ?_
  have c₃ := c₂.chg h₃
  have cval : Lanes (s₃.v .v23) C := by
    rw [h₃.get .v23, h₂.get .v23, h₁.get .v23]; exact hc'
  refine reduce_ok (d := .v23) (by decide) (by decide) (by decide) c₃ cval
    (fun e he => by have := bc e he; omega) fun s₄ h₄ l₄ => ?_
  refine k s₄ (((h₁.trans h₂.chg).trans h₃).trans h₄).mono ?_ l₄
  rw [h₄.get .v21]
  refine l₃.congr fun e he => ?_
  rw [Nat.add_mod, Nat.mul_mod, (b₁ e he).2, ← Nat.mul_mod, ← Nat.add_mod]

end VG.Proof.MlKem.AArch64.Dot
