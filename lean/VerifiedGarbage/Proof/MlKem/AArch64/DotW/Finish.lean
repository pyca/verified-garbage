module

public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Term
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: the terms and the finish

All the terms (`termsW_ok`), and the reduction of each group of sums
(`finishR_ok`: `finish` of `dot` with any registers).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Dot

theorem termsW_ok {bf bg : Reg} (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {s : State} {lo hi : Nat → Sums} {n : Nat}
    (hc : VConsts s) (ha : AccumW s lo hi) (hlo : ∀ e < 4, (lo e).Bounded n)
    (hhi : ∀ e < 4, (hi e).Bounded n) (hn : n + terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInputW s bf bg fg (F fg) (G fg)) :
    WP isa (.block (terms.flatMap (Impl.MlKem.AArch64.DotW.termW bf bg))) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧
        AccumW s' (sumTerms terms F G lo) (sumTerms terms (fun fg => upper (F fg)) (fun fg => upper (G fg)) hi) := by
  induction terms generalizing s lo hi n with
  | nil => exact wp_nil ⟨Only.refl _ _, hc, ha⟩
  | cons fg terms ih =>
    simp only [List.length_cons] at hn
    rw [List.flatMap_cons, WP.block_append_iff]
    have h := hin fg (by simp)
    refine WP.mono (fullTermW_ok h hc ha hlo hhi (by omega)) fun s₁ ⟨hk, hc₁, ha₁⟩ => ?_
    refine WP.mono (ih hc₁ ha₁ (n := n + 1)
      (fun e he => (hlo e he).next (h.boundF _ (by omega)) (h.boundF _ (by omega))
        (h.boundG _ (by omega)) (h.boundG _ (by omega)))
      (fun e he => (hhi e he).next (h.boundF _ (by omega)) (h.boundF _ (by omega))
        (h.boundG _ (by omega)) (h.boundG _ (by omega)))
      (by omega) (fun fg hf => (hin fg (by simp [hf])).keep hk)) fun s₂ ⟨hk₂, hc₂, ha₂⟩ => ?_
    exact ⟨(hk.trans hk₂).mono (by simp), hc₂, ha₂⟩

section
variable {rest : List Instr} {Q : State → Prop}

/-- `sqdmulh t, d, M; mls d, t, q; vcsub d t`: `d mod q`, for lanes less than `2³¹`. -/
theorem reduceR_ok {s : State} {d t : VReg} (hdt : d ≠ t := by decide) (ht16 : t ≠ .v16 := by decide)
    (ht17 : t ≠ .v17 := by decide) (hd16 : d ≠ .v16 := by decide) (hd17 : d ≠ .v17 := by decide)
    (hc : VConsts s) {f : Nat → Nat} (hf : Lanes (s.v d) f) (hlt : ∀ e < 4, f e < 2 ^ 31)
    (k : ∀ s', VChg [t, d] s s' → Lanes (s'.v d) (fun e => f e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block ([.vop (.sqdmulh t d .v17), .vop (.mls d t .v16)] ++ vcsub d t ++ rest)) s Q := by
  simp only [List.cons_append, List.nil_append]
  refine vbar_ok hdt ht16 ht17 (hc := hc) (hf := hf) (hlt := hlt) (k := fun s₁ h₁ l₁ b₁ => ?_)
  have c₁ := hc.chg h₁ (by simp [hd16.symm, ht16.symm]) (by simp [hd17.symm, ht17.symm])
  refine vcsub_ok hdt c₁.q l₁ (fun e he => (b₁ e he).1) fun s₂ h₂ l₂ => ?_
  exact k s₂ ((h₁.trans h₂).mono (by simp)) (l₂.congr fun e he => (b₁ e he).2)

/-- `finishR a b c g t`: `(A + B · Γ) mod q` in `a` and `C mod q` in `c`. -/
theorem finishR_ok {s : State} {a b c g t : VReg}
    (hab : a ≠ b := by decide) (hac : a ≠ c := by decide) (hat : a ≠ t := by decide)
    (hbc : b ≠ c := by decide) (hbt : b ≠ t := by decide) (hct : c ≠ t := by decide)
    (hgb : g ≠ b := by decide) (hgt : g ≠ t := by decide)
    (ha16 : a ≠ .v16 := by decide) (ha17 : a ≠ .v17 := by decide)
    (hb16 : b ≠ .v16 := by decide) (hb17 : b ≠ .v17 := by decide)
    (hc16 : c ≠ .v16 := by decide) (hc17 : c ≠ .v17 := by decide)
    (ht16 : t ≠ .v16 := by decide) (ht17 : t ≠ .v17 := by decide)
    (hc : VConsts s) {A B C G : Nat → Nat}
    (la : Lanes (s.v a) A) (lb : Lanes (s.v b) B) (lc : Lanes (s.v c) C) (lg : Lanes (s.v g) G)
    (ba : ∀ e < 4, A e ≤ 4 * 3329 * 3329) (bb : ∀ e < 4, B e ≤ 4 * 3329 * 3329)
    (bc : ∀ e < 4, C e ≤ 8 * 3329 * 3329) (bg : ∀ e < 4, G e < 3329)
    (k : ∀ s', VChg ([t, b] ++ [a] ++ [t, a] ++ [t, c]) s s' →
      Lanes (s'.v a) (fun e => (A e + B e * G e) % 3329) →
      Lanes (s'.v c) (fun e => C e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.DotW.finishR a b c g t ++ rest)) s Q := by
  simp only [Impl.MlKem.AArch64.DotW.finishR, List.append_assoc, List.cons_append, List.nil_append]
  refine vbar_ok (d := b) (t := t) hbt ht16 ht17 (hc := hc) (hf := lb)
    (hlt := fun e he => by have := bb e he; omega) (k := fun s₁ h₁ l₁ b₁ => ?_)
  have a₁ : Lanes (s₁.v a) A := by rw [h₁.get a (by simp [hat, hab])]; exact la
  have g₁ : Lanes (s₁.v g) G := by rw [h₁.get g (by simp [hgt, hgb])]; exact lg
  let R := fun e => B e - B e * 645083 / 2 ^ 31 * 3329
  try rewrite [show fun e => B e - B e * 645083 / 2 ^ 31 * 3329 = R from rfl] at *
  have br : ∀ e < 4, R e * G e ≤ 2 * 3329 * 3329 := fun e he =>
    Nat.mul_le_mul (Nat.le_of_lt (b₁ e he).1) (Nat.le_of_lt (bg e he))
  have bylt : ∀ e < 4, A e + R e * G e < 2 ^ 31 := fun e he => by
    have := ba e he; have := br e he; omega
  refine wp_vop (d := a) rfl fun s₂ h₂ => ?_
  have l₂ : Lanes (s₂.v a) (fun e => A e + R e * G e) := by
    rw [h₂.v]
    exact (lanes_mla a₁ l₁ g₁).congr fun e he => by
      have := bylt e he
      rw [Nat.mod_eq_of_lt (show R e * G e < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt (show A e + R e * G e < 2 ^ 32 by omega)]
  have c₂ := (hc.chg h₁ (by simp [hb16.symm, ht16.symm]) (by simp [hb17.symm, ht17.symm])).chg h₂.chg
    (by simp [ha16.symm]) (by simp [ha17.symm])
  rw [← List.cons_append, ← List.cons_append]
  refine reduceR_ok (d := a) (t := t) hat ht16 ht17 ha16 ha17 c₂ l₂ bylt fun s₃ h₃ l₃ => ?_
  have c₃ := c₂.chg h₃ (by simp [ha16.symm, ht16.symm]) (by simp [ha17.symm, ht17.symm])
  have cval : Lanes (s₃.v c) C := by
    rw [h₃.get c (by simp [hct, hac.symm]), h₂.get c hac.symm, h₁.get c (by simp [hct, hbc.symm])]
    exact lc
  rw [← List.cons_append, ← List.cons_append]
  refine reduceR_ok (d := c) (t := t) hct ht16 ht17 hc16 hc17 c₃ cval
    (fun e he => by have := bc e he; omega) fun s₄ h₄ l₄ => ?_
  refine k s₄ (((h₁.trans h₂.chg).trans h₃).trans h₄) ?_ l₄
  rw [h₄.get a (by simp [hat, hac])]
  refine l₃.congr fun e he => ?_
  rw [Nat.add_mod, Nat.mul_mod, (b₁ e he).2, ← Nat.mul_mod, ← Nat.add_mod]

end

end VG.Proof.MlKem.AArch64.DotW
