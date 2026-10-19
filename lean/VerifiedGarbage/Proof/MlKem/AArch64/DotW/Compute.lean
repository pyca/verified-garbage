module
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Term

import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Finish
import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: an iteration's sums

`clearW`, the terms, the two tables of `γ` and the two finishes (`computeW_ok`):
the even and odd results of pairs `0 … 3` in `v21`, `v23` and of pairs `4 … 7`
in `v25`, `v27`, as `dot`'s `evenResult` and `oddResult`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

section
variable {rest : List Instr} {Q : State → Prop}

theorem clearW_ok {s : State}
    (k : ∀ s', VChg [.v21, .v22, .v23, .v25, .v26, .v27] s s' → AccumW s' zeroSums zeroSums →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.DotW.clearW ++ rest)) s Q := by
  simp only [Impl.MlKem.AArch64.DotW.clearW, List.cons_append, List.nil_append]
  refine wp_vop (d := .v21) rfl fun s₁ h₁ => wp_vop (d := .v22) rfl fun s₂ h₂ =>
    wp_vop (d := .v23) rfl fun s₃ h₃ => wp_vop (d := .v25) rfl fun s₄ h₄ =>
    wp_vop (d := .v26) rfl fun s₅ h₅ => wp_vop (d := .v27) rfl fun s₆ h₆ => ?_
  refine k s₆ (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg).trans h₆.chg).mono
    ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [h₆.get .v21, h₅.get .v21, h₄.get .v21, h₃.get .v21, h₂.get .v21, h₁.v]; exact zeroLanes
  · rw [h₆.get .v22, h₅.get .v22, h₄.get .v22, h₃.get .v22, h₂.v]; exact zeroLanes
  · rw [h₆.get .v23, h₅.get .v23, h₄.get .v23, h₃.v]; exact zeroLanes
  · rw [h₆.get .v25, h₅.get .v25, h₄.v]; exact zeroLanes
  · rw [h₆.get .v26, h₅.v]; exact zeroLanes
  · rw [h₆.v]; exact zeroLanes

end

def computeW (bf bg : Reg) (terms : List (Nat × Nat)) : List Instr :=
  Impl.MlKem.AArch64.DotW.clearW ++ terms.flatMap (Impl.MlKem.AArch64.DotW.termW bf bg) ++
    [.ldrq .v18 .x3 0, .ldrq .v28 .x3 16] ++
    Impl.MlKem.AArch64.DotW.finishR .v21 .v22 .v23 .v18 .v24 ++
    Impl.MlKem.AArch64.DotW.finishR .v25 .v26 .v27 .v28 .v24

theorem computeW_ok {s : State} {rF rG : Reg} (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Nat → Nat} {Γ Γ' : Nat → Nat}
    (hc : VConsts s) (hn : terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInputW s rF rG fg (F fg) (G fg))
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * i)) 16)
    (hg : Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 0) 16) Γ)
    (hg' : Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 16) 16) Γ')
    (bg : ∀ e < 4, Γ e < 3329) (bg' : ∀ e < 4, Γ' e < 3329) :
    WP isa (.block (computeW rF rG terms)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧
      Lanes (s'.v .v21) (evenResult terms F G Γ) ∧ Lanes (s'.v .v23) (oddResult terms F G) ∧
      Lanes (s'.v .v25) (evenResult terms (fun fg => upper (F fg)) (fun fg => upper (G fg)) Γ') ∧
      Lanes (s'.v .v27) (oddResult terms (fun fg => upper (F fg)) (fun fg => upper (G fg))) := by
  simp only [computeW, List.append_assoc]
  refine clearW_ok fun s₁ h₁ a₁ => ?_
  have k₁ := only_vchg h₁
  have input₁ : ∀ fg ∈ terms, TermInputW s₁ rF rG fg (F fg) (G fg) :=
    fun fg hf => (hin fg hf).keep (k₁.mono (by simp))
  rw [WP.block_append_iff]
  have z : ∀ e < 4, (zeroSums e).Bounded 0 := fun _ _ => by simp only [zeroSums, Sums.Bounded]; decide
  refine WP.mono (termsW_ok terms (hc.chg h₁) a₁ z z (by simpa only [Nat.zero_add] using hn) input₁)
    fun s₂ ⟨k₂, c₂, a₂⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) rfl
    (by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr, k₂.get .x3, k₁.get .x3]; exact hr 0 (by decide)) fun s₃ h₃ => ?_
  refine wp_ldrq (by decide) rfl
    (by rw [h₃.rd, h₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr, h₃.gpr, k₂.get .x3, k₁.get .x3]; exact hr 1 (by decide))
    fun s₄ h₄ => ?_
  have g₄ : Lanes (s₄.v .v18) Γ := by
    rw [h₄.get .v18, h₃.v, k₂.mem, k₁.mem, k₂.get .x3, k₁.get .x3]; exact hg
  have g₄' : Lanes (s₄.v .v28) Γ' := by
    rw [h₄.v, h₃.mem, k₂.mem, k₁.mem, h₃.gpr, k₂.get .x3, k₁.get .x3]; exact hg'
  have blo : ∀ e < 4, (sumTerms terms F G zeroSums e).Bounded terms.length := by
    simpa only [Nat.zero_add] using sumTerms_bound terms (n := 0) (a := zeroSums) z
      (fun fg hf e he => (hin fg hf).boundF e (by omega)) (fun fg hf e he => (hin fg hf).boundG e (by omega))
  have bhi : ∀ e < 4, (sumTerms terms (fun fg => upper (F fg)) (fun fg => upper (G fg)) zeroSums e).Bounded
      terms.length := by
    simpa only [Nat.zero_add] using sumTerms_bound terms (n := 0) (a := zeroSums) z
      (fun fg hf e he => (hin fg hf).boundF (8 + e) (by omega))
      (fun fg hf e he => (hin fg hf).boundG (8 + e) (by omega))
  have C₄ := h₃.chg.trans h₄.chg
  obtain ⟨⟨a21, a22, a23⟩, a25, a26, a27⟩ := a₂
  have c₄ := c₂.chg C₄
  refine finishR_ok (a := .v21) (b := .v22) (c := .v23) (g := .v18) (t := .v24) (hc := c₄)
    (la := by rw [C₄.get .v21]; exact a21) (lb := by rw [C₄.get .v22]; exact a22)
    (lc := by rw [C₄.get .v23]; exact a23) (lg := g₄)
    (ba := fun e he => ((blo e he).machine hn).1) (bb := fun e he => ((blo e he).machine hn).2.1)
    (bc := fun e he => ((blo e he).machine hn).2.2) (bg := bg) (k := fun s₅ h₅ l21 l23 => ?_)
  rw [← List.append_nil (Impl.MlKem.AArch64.DotW.finishR _ _ _ _ _)]
  refine finishR_ok (a := .v25) (b := .v26) (c := .v27) (g := .v28) (t := .v24) (hc := c₄.chg h₅)
    (la := by rw [h₅.get .v25, C₄.get .v25]; exact a25) (lb := by rw [h₅.get .v26, C₄.get .v26]; exact a26)
    (lc := by rw [h₅.get .v27, C₄.get .v27]; exact a27) (lg := by rw [h₅.get .v28]; exact g₄')
    (ba := fun e he => ((bhi e he).machine hn).1) (bb := fun e he => ((bhi e he).machine hn).2.1)
    (bc := fun e he => ((bhi e he).machine hn).2.2) (bg := bg') (k := fun s₆ h₆ l25 l27 => wp_nil ?_)
  exact ⟨((((k₁.trans k₂).trans (only_vchg C₄)).trans (only_vchg h₅)).trans (only_vchg h₆)).mono (by simp),
    (c₄.chg h₅).chg h₆, by rw [h₆.get .v21]; exact l21, by rw [h₆.get .v23]; exact l23, l25, l27⟩

end VG.Proof.MlKem.AArch64.DotW
