module
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec


/-! Exact nonwrapping fused accumulation of one polynomial term. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def accumulate : List Instr :=
  [.vop (.mla .v21 .v6 .v19), .vop (.mla .v22 .v7 .v20),
   .vop (.mla .v23 .v6 .v20), .vop (.mla .v23 .v7 .v19)]

theorem mla_ok {s : State} {Q : State → Prop} {rest : List Instr}
    {d n m : VReg} {a f g : Nat → Nat}
    (ha : Lanes (s.v d) a) (hf : Lanes (s.v n) f) (hg : Lanes (s.v m) g)
    (hlt : ∀ e < 4, a e + f e * g e < 2 ^ 32)
    (k : ∀ s', VUpd s s' d (mapWords3 (fun a x y => a + x*y) (s.v d) (s.v n) (s.v m)) →
      Lanes (s'.v d) (fun e => a e + f e * g e) → WP isa (.block rest) s' Q) :
    WP isa (.block (.vop (.mla d n m) :: rest)) s Q := by
  refine wp_vop (d := d) rfl fun s' h => k s' h ?_
  rw [h.v]
  refine (lanes_mla ha hf hg).congr fun e he => ?_
  have h := hlt e he
  rw [Nat.mod_eq_of_lt (show f e * g e < 2 ^ 32 by omega), Nat.mod_eq_of_lt h]

theorem accumulate_ok {rest : List Instr} {s : State} {Q : State → Prop}
    {A B C FE FO GE GO : Nat → Nat}
    (ha : Lanes (s.v .v21) A) (hb : Lanes (s.v .v22) B) (hc : Lanes (s.v .v23) C)
    (hfe : Lanes (s.v .v6) FE) (hfo : Lanes (s.v .v7) FO)
    (hge : Lanes (s.v .v19) GE) (hgo : Lanes (s.v .v20) GO)
    (ba : ∀ e < 4, A e + FE e * GE e < 2 ^ 32)
    (bb : ∀ e < 4, B e + FO e * GO e < 2 ^ 32)
    (bc : ∀ e < 4, C e + FE e * GO e + FO e * GE e < 2 ^ 32)
    (k : ∀ s', VChg [.v21, .v22, .v23] s s' →
      Lanes (s'.v .v21) (fun e => A e + FE e * GE e) →
      Lanes (s'.v .v22) (fun e => B e + FO e * GO e) →
      Lanes (s'.v .v23) (fun e => C e + FE e * GO e + FO e * GE e) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (accumulate ++ rest)) s Q := by
  simp only [accumulate, List.cons_append, List.nil_append]
  refine mla_ok ha hfe hge ba fun s₁ h₁ l₁ => ?_
  have b₁ : Lanes (s₁.v .v22) B := by rw [h₁.get .v22]; exact hb
  have fo₁ : Lanes (s₁.v .v7) FO := by rw [h₁.get .v7]; exact hfo
  have go₁ : Lanes (s₁.v .v20) GO := by rw [h₁.get .v20]; exact hgo
  refine mla_ok b₁ fo₁ go₁ bb fun s₂ h₂ l₂ => ?_
  have c₂ : Lanes (s₂.v .v23) C := by rw [h₂.get .v23, h₁.get .v23]; exact hc
  have fe₂ : Lanes (s₂.v .v6) FE := by rw [h₂.get .v6, h₁.get .v6]; exact hfe
  have go₂ : Lanes (s₂.v .v20) GO := by rw [h₂.get .v20]; exact go₁
  refine mla_ok c₂ fe₂ go₂ (fun e he => by have := bc e he; omega) fun s₃ h₃ l₃ => ?_
  have fo₃ : Lanes (s₃.v .v7) FO := by rw [h₃.get .v7, h₂.get .v7]; exact fo₁
  have ge₃ : Lanes (s₃.v .v19) GE := by rw [h₃.get .v19, h₂.get .v19, h₁.get .v19]; exact hge
  refine mla_ok l₃ fo₃ ge₃ bc fun s₄ h₄ l₄ => ?_
  refine k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).mono ?_ ?_ l₄
  · rw [h₄.get .v21, h₃.get .v21, h₂.get .v21]; exact l₁
  · rw [h₄.get .v22, h₃.get .v22]; exact l₂

end VG.Proof.MlKem.AArch64.Dot
