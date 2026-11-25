module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Rows
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Ed25519 and X25519 on AArch64: the inversion's update

`(f, g)` after a batch's update (`updateFG_ok`), and `(a, b)` modulo `p` (`updateAB_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Divstep
open VG.Proof.Ed25519.AArch64 Word64
open VG.Proof.Mont.AArch64 (KeepRegs)

variable {large : Bool}

/-- The registers the update writes but `x16`. -/
abbrev updRegs : List Reg := [.x2, .x3, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x17]

theorem sv_mul (u F : Nat) :
    ((u * F : Nat) : Int) - 2 ^ 256 * ((if 2 ^ 255 ≤ F then u else 0 : Nat) : Int) = u * sv F := by
  unfold sv
  by_cases h : 2 ^ 255 ≤ F
  · simp only [h, ↓reduceIte, show ¬ F < 2 ^ 255 by omega_using [h]]
    push_cast; ring
  · simp only [h, ↓reduceIte, show F < 2 ^ 255 by omega_using [h]]
    push_cast; ring

theorem sv_split (F : Nat) : ∃ b : Int, (F : Int) = sv F + 2 ^ 256 * b := by
  unfold sv
  split
  · exact ⟨0, by omega_using []⟩
  · exact ⟨1, by omega_using []⟩

theorem sv_eq {L : Nat} {f k : Int} (hL : L < 2 ^ 256) (hf : |f| < 2 ^ 255) (h : (L : Int) = f + 2 ^ 256 * k) :
    sv L = f := by
  rw [abs_lt] at hf
  unfold sv
  split <;> omega_arith

/-- The arithmetic of `rowFG`. -/
theorem rowFG_math {u v F G S r1 r2 r3 r4 l5 l6 k1 k2 k3 k5 k6 ks : Nat} {U V f' : Int}
    (hu : (u : Int) = U + 2 ^ 59) (hv : (v : Int) = V + 2 ^ 59)
    (h1 : r1 = u * F) (h2 : r2 + 2 ^ 256 * (if 2 ^ 255 ≤ F then u else 0) = r1 + 2 ^ 256 * 2 ^ 64 * k1)
    (h3 : r3 + 2 ^ 256 * 2 ^ 64 * k2 = r2 + v * G)
    (h4 : r4 + 2 ^ 256 * (if 2 ^ 255 ≤ G then v else 0) = r3 + 2 ^ 256 * 2 ^ 64 * k3)
    (h5 : l5 + 2 ^ 256 * k5 = r4 / 2 ^ 59) (h6 : l6 + S = l5 + 2 ^ 256 * k6)
    (hS : S + 2 ^ 256 * ks = F + G) (hf' : 2 ^ 59 * f' = U * sv F + V * sv G) (hb : |f'| < 2 ^ 255)
    (hl : l6 < 2 ^ 256) : sv l6 = f' := by
  have e1 := sv_mul u F
  have e2 := sv_mul v G
  obtain ⟨b, hb1⟩ := sv_split F
  obtain ⟨c, hc1⟩ := sv_split G
  have x1 : (u : Int) * sv F = U * sv F + 2 ^ 59 * sv F := by rw [hu]; ring
  have x2 : (v : Int) * sv G = V * sv G + 2 ^ 59 * sv G := by rw [hv]; ring
  have r : (r4 : Int) = 2 ^ 59 * (f' + sv F + sv G) + 2 ^ 59 * (2 ^ 256 * (32 * ((k1 : Int) - k2 + k3))) := by
    rw [h1] at h2
    generalize u * F = A at *
    generalize v * G = B at *
    generalize (u : Int) * sv F = A' at *
    generalize (v : Int) * sv G = B' at *
    generalize U * sv F = A'' at *
    generalize V * sv G = B'' at *
    generalize (if 2 ^ 255 ≤ F then u else 0) = m at *
    generalize (if 2 ^ 255 ≤ G then v else 0) = n at *
    omega_using [h2, h3, h4, hf', e1, e2, x1, x2]
  generalize sv F = f at *
  generalize sv G = g at *
  refine sv_eq (k := 32 * ((k1 : Int) - k2 + k3) - k5 + k6 + ks - b - c) hl hb ?_
  omega_using [r, h5, h6, hS, hb1, hc1]

/-- A row of `f` and `g`. -/
theorem rowFG_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x16 = 0) {u v : Reg}
    (huv : u = .x4 ∧ v = .x5 ∨ u = .x6 ∧ v = .x7) {o : Nat} (ho : Off4 o) {U V f' : Int}
    (hu : ((s.gpr u).toNat : Int) = U + 2 ^ 59) (hv : ((s.gpr v).toNat : Int) = V + 2 ^ 59)
    (hS : ∃ k, fe s.mem base oS + 2 ^ 256 * k = fe s.mem base oF + fe s.mem base oG)
    (hf' : 2 ^ 59 * f' = U * sv (fe s.mem base oF) + V * sv (fe s.mem base oG)) (hb : |f'| < 2 ^ 255) :
    WP isa (.block (rowFG u v o)) s fun t =>
      sv (fe t.mem base o) = f' ∧ Outside base o 32 s.mem t.mem ∧ KeepRegs updRegs s t := by
  obtain ⟨ks, hS⟩ := hS
  have D : (u = .x4 ∨ u = .x6) ∧ (v = .x5 ∨ v = .x7) ∧ u ∈ [Reg.x4, .x5, .x6, .x7] ∧ v ∈ [Reg.x4, .x5, .x6, .x7] ∧
      u ∉ updRegs ∧ v ∉ updRegs := by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨Du, Dv, Mu, Mv, Nu, Nv⟩ := D
  simp only [rowFG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok hs (o := oF) (by decide)) fun s₁ ⟨v₁, q₁⟩ => ?_
  have k₁ : Keeps updRegs s s₁ := q₁.mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulFirst_ok s₁ Du (by rw [k₁.gpr _ (by decide), hz])) fun s₂ ⟨v₂, q₂⟩ => ?_
  have k₂ : Keeps updRegs s s₂ := k₁.trans (q₂.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (signed_ok s₂ Mu (by rw [k₂.gpr _ (by decide), hz])) fun s₃ ⟨⟨n₃, v₃⟩, q₃⟩ => ?_
  have k₃ : Keeps updRegs s s₃ := k₂.trans (q₃.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok (hs.of_keeps k₃ (by decide)) (o := oG) (by decide)) fun s₄ ⟨v₄, q₄⟩ => ?_
  have k₄ : Keeps updRegs s s₄ := k₃.trans (q₄.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (mulAcc_ok s₄ Dv (by rw [k₄.gpr _ (by decide), hz])) fun s₅ ⟨⟨n₅, v₅⟩, q₅⟩ => ?_
  have k₅ : Keeps updRegs s s₅ := k₄.trans (q₅.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (signed_ok s₅ Mv (by rw [k₅.gpr _ (by decide), hz])) fun s₆ ⟨⟨n₆, v₆⟩, q₆⟩ => ?_
  have k₆ : Keeps updRegs s s₆ := k₅.trans (q₆.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok (hs.of_keeps k₆ (by decide)) (o := oS) (by decide)) fun s₇ ⟨v₇, q₇⟩ => ?_
  have k₇ : Keeps updRegs s s₇ := k₆.trans (q₇.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (shift_ok s₇) fun s₈ ⟨⟨n₈, v₈⟩, q₈⟩ => ?_
  have k₈ : Keeps updRegs s s₈ := k₇.trans (q₈.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (subOpd_ok s₈) fun s₉ ⟨⟨n₉, v₉⟩, q₉⟩ => ?_
  have k₉ : Keeps updRegs s s₉ := k₈.trans (q₉.mono (by decide))
  refine WP.mono (stp4_ok (hs.of_keeps k₉ (by decide)) ho _ _ _ _) fun t ht => ?_
  have hfe : fe t.mem base o = lo s₉ := by
    rw [ht]; exact fe_st4 _ _ (by omega_using [ho.2]) _ _ _ _
  rw [opd_keeps q₂ (by decide)] at v₃
  rw [k₁.gpr _ Nu] at v₂
  rw [k₂.gpr _ Nu] at v₃
  rw [row_keeps q₄ (by decide), k₄.gpr _ Nv, v₄, k₃.mem] at v₅
  rw [opd_keeps q₅ (by decide), k₅.gpr _ Nv, v₄, k₃.mem] at v₆
  rw [v₁] at v₂ v₃
  rw [row_keeps q₇ (by decide)] at v₈
  rw [opd_keeps q₈ (by decide), v₇, k₆.mem] at v₉
  refine ⟨?_, ?_, ⟨fun r hr => by rw [ht]; exact k₉.gpr r hr, by rw [ht]; exact k₉.rd, by rw [ht]; exact k₉.wr,
    by rw [ht]; exact k₉.sp⟩⟩
  · rw [hfe]
    exact rowFG_math hu hv v₂ v₃ v₅ v₆ v₈ v₉ hS hf' hb (lo_lt _)
  · rw [ht, ← k₉.mem]
    exact st4_outside _ _ (by omega_using [ho.2]) _ _ _ _

/-- A bound of `a` and `b`. -/
abbrev abMax : Nat := 2 ^ 255 + 2 ^ 67

/-- The offset of `a` and `b`'s rows in memory, five words. -/
def offE (m : Mem) (base : Addr) : Nat := fe m base oE + 2 ^ 256 * (word m base (oE + 32)).toNat

/-- The arithmetic of `rowAB`. -/
theorem rowAB_math {u v A B E r1 r2 k2 ke : Nat} {U V : Int}
    (hu : (u : Int) = U + 2 ^ 59) (hv : (v : Int) = V + 2 ^ 59) (huv : |U| + |V| ≤ 2 ^ 59)
    (hA : A < abMax) (hB : B < abMax)
    (h1 : r1 = u * A) (h2 : r2 + 2 ^ 256 * 2 ^ 64 * k2 = r1 + v * B)
    (hE : E + 2 ^ 59 * (A + B) = 2 ^ 59 * (2 ^ 256 - 38) + 2 ^ 256 * 2 ^ 64 * ke) :
    ∃ W K : Nat, r2 + E = W + 2 ^ 256 * 2 ^ 64 * K ∧ W < 2 ^ 256 * 2 ^ 61 ∧
      (W : Int) = U * A + V * B + 2 ^ 60 * (2 ^ 255 - 19) := by
  have hA' : |(A : Int)| ≤ abMax := by rw [abs_of_nonneg (by omega_using [])]; omega_using [hA]
  have hB' : |(B : Int)| ≤ abMax := by rw [abs_of_nonneg (by omega_using [])]; omega_using [hB]
  have hc := abs_le.mp (Divstep.comb_le huv hA' hB')
  have x1 : ((u * A : Nat) : Int) = U * A + 2 ^ 59 * A := by rw [Nat.cast_mul, hu]; ring
  have x2 : ((v * B : Nat) : Int) = V * B + 2 ^ 59 * B := by rw [Nat.cast_mul, hv]; ring
  subst h1
  generalize U * (A : Int) = X at *
  generalize V * (B : Int) = Y at *
  generalize u * A = P at *
  generalize v * B = Q at *
  have hM : ((abMax : Nat) : Int) = 2 ^ 255 + 2 ^ 67 := by decide
  rw [hM] at hc
  have hc1 := hc.1
  have hc2 := hc.2
  obtain ⟨W, hW⟩ : ∃ W : Nat, (W : Int) = X + Y + 2 ^ 60 * (2 ^ 255 - 19) :=
    ⟨(X + Y + 2 ^ 60 * (2 ^ 255 - 19)).toNat, by omega_using [hc1, hc2]⟩
  have lW : W < 2 ^ 256 * 2 ^ 61 := by omega_using [hW, hc2]
  refine ⟨W, ke - k2, ?_, lW, hW⟩
  omega_using [hW, lW, h2, hE, x1, x2]

/-- A row of `a` and `b`. -/
theorem rowAB_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x16 = 0) (h17 : s.gpr .x17 = 19)
    {u v : Reg} (huv : u = .x4 ∧ v = .x5 ∨ u = .x6 ∧ v = .x7) {o : Nat} (ho : Off4 o) {U V : Int}
    (hu : ((s.gpr u).toNat : Int) = U + 2 ^ 59) (hv : ((s.gpr v).toNat : Int) = V + 2 ^ 59)
    (hUV : |U| + |V| ≤ 2 ^ 59) (hA : fe s.mem base oA < abMax) (hB : fe s.mem base oB < abMax)
    (hE : ∃ k, offE s.mem base + 2 ^ 59 * (fe s.mem base oA + fe s.mem base oB) =
      2 ^ 59 * (2 ^ 256 - 38) + 2 ^ 256 * 2 ^ 64 * k) :
    WP isa (.block (rowAB u v o)) s fun t =>
      fe t.mem base o < abMax ∧
      (∃ m : Int, (fe t.mem base o : Int) = U * fe s.mem base oA + V * fe s.mem base oB + (2 ^ 255 - 19) * m) ∧
      Outside base o 32 s.mem t.mem ∧ t.gpr .x17 = 19 ∧ KeepRegs updRegs s t := by
  obtain ⟨ke, hE⟩ := hE
  have D : (u = .x4 ∨ u = .x6) ∧ (v = .x5 ∨ v = .x7) ∧ u ∉ updRegs ∧ v ∉ updRegs := by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨Du, Dv, Nu, Nv⟩ := D
  let rs : List Reg := [.x2, .x3, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15]
  have hsub : ∀ r, r ∉ updRegs → r ∉ rs := fun r h h' => h ((by decide : ∀ a ∈ rs, a ∈ updRegs) r h')
  simp only [rowAB, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok hs (o := oA) (by decide)) fun s₁ ⟨v₁, q₁⟩ => ?_
  have k₁ : Keeps rs s s₁ := q₁.mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulFirst_ok s₁ Du (by rw [k₁.gpr _ (by decide), hz])) fun s₂ ⟨v₂, q₂⟩ => ?_
  have k₂ : Keeps rs s s₂ := k₁.trans (q₂.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok (hs.of_keeps k₂ (by decide)) (o := oB) (by decide)) fun s₃ ⟨v₃, q₃⟩ => ?_
  have k₃ : Keeps rs s s₃ := k₂.trans (q₃.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (mulAcc_ok s₃ Dv (by rw [k₃.gpr _ (by decide), hz])) fun s₄ ⟨⟨n₄, v₄⟩, q₄⟩ => ?_
  have k₄ : Keeps rs s s₄ := k₃.trans (q₄.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok (hs.of_keeps k₄ (by decide)) (o := oE) (by decide)) fun s₅ ⟨v₅, q₅⟩ => ?_
  have k₅ : Keeps rs s s₅ := k₄.trans (q₅.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs.of_keeps k₅ (by decide)) (d := oE + 32) (by decide) (by
    have := workSize_ge large; unfold oE; omega_using [this]) .x15) fun s₆ ⟨v₆, q₆⟩ => ?_
  have k₆ : Keeps rs s s₆ := k₅.trans (q₆.mono (by decide))
  rw [row_keeps q₃ (by decide), v₂, v₁, k₃.gpr _ (hsub _ Nv), v₃, k₂.mem, k₁.gpr _ (hsub _ Nu)] at v₄
  obtain ⟨W, K, hWK, lW, eW⟩ := rowAB_math hu hv hUV hA hB rfl v₄ hE
  have ho5 : off5 s₆ = offE s.mem base := by
    unfold off5 offE
    rw [opd_keeps q₆ (by decide), v₅, v₆, k₅.mem, k₄.mem]
  have hr : row s₆ = row s₄ := by rw [row_keeps q₆ (by decide), row_keeps q₅ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok s₆ (by rw [k₆.gpr _ (by decide), hz]) (by rw [k₆.gpr _ (by decide), h17])
    (by rw [hr, ho5]; exact hWK) lW) fun s₇ ⟨v₇, q₇⟩ => ?_
  have k₇ : Keeps rs s s₇ := k₆.trans (q₇.mono (by decide))
  refine WP.mono (stp4_ok (hs.of_keeps k₇ (by decide)) ho _ _ _ _) fun t ht => ?_
  have hfe : fe t.mem base o = lo s₇ := by
    rw [ht]; exact fe_st4 _ _ (by omega_using [ho.2]) _ _ _ _
  refine ⟨?_, ⟨2 ^ 60 - (W / 2 ^ 255 : Nat), ?_⟩, ?_, ?_, ⟨fun r hr => ?_, by rw [ht]; exact k₇.rd, by rw [ht]; exact k₇.wr,
    by rw [ht]; exact k₇.sp⟩⟩
  · rw [hfe, v₇]; unfold abMax; omega_using [lW]
  · rw [hfe, v₇]
    generalize U * (fe s.mem base oA : Int) = X at *
    generalize V * (fe s.mem base oB : Int) = Y at *
    omega_using [eW]
  · rw [ht, ← k₇.mem]
    exact st4_outside _ _ (by omega_using [ho.2]) _ _ _ _
  · rw [ht]; exact (k₇.gpr _ (by decide)).trans h17
  · rw [ht]; exact k₇.gpr r (hsub r hr)

/-! ## The whole update -/

theorem copy4_ok {s : State} {base : Addr} (hs : Scr s base large) {d o : Nat} (hd : Off4 d) (ho : Off4 o) :
    WP isa (.block (copy4 d o)) s fun t =>
      fe t.mem base d = fe s.mem base o ∧ Outside base d 32 s.mem t.mem ∧ KeepRegs updRegs s t := by
  rw [copy4, WP.block_append_iff]
  refine WP.mono (ldOpd_ok hs ho) fun s₁ ⟨v₁, q₁⟩ => ?_
  have k₁ : Keeps updRegs s s₁ := q₁.mono (by decide)
  refine WP.mono (stp4_ok (hs.of_keeps k₁ (by decide)) hd _ _ _ _) fun t ht => ⟨?_, ?_, fun r hr => by
    rw [ht]; exact k₁.gpr r hr, by rw [ht]; exact k₁.rd, by rw [ht]; exact k₁.wr, by rw [ht]; exact k₁.sp⟩
  · rw [ht, ← v₁]; exact fe_st4 _ _ (by omega_using [hd.2]) _ _ _ _
  · rw [ht, ← k₁.mem]; exact st4_outside _ _ (by omega_using [hd.2]) _ _ _ _

theorem sumFG_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block sumFG) s fun t =>
      (∃ k, fe t.mem base oS + 2 ^ 256 * k = fe s.mem base oF + fe s.mem base oG) ∧
      Outside base oS 32 s.mem t.mem ∧ KeepRegs updRegs s t := by
  simp only [sumFG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldp4_ok hs (o := oF) (by decide) (by decide)) fun s₁ ⟨a, b, c, d, q₁⟩ => ?_
  have k₁ : Keeps updRegs s s₁ := q₁.mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok (hs.of_keeps k₁ (by decide)) (o := oG) (by decide)) fun s₂ ⟨v₂, q₂⟩ => ?_
  have k₂ : Keeps updRegs s s₂ := k₁.trans (q₂.mono (by decide))
  have l₂ : lo s₂ = fe s.mem base oF := by
    unfold lo
    rw [q₂.gpr _ (by decide), q₂.gpr _ (by decide), q₂.gpr _ (by decide), q₂.gpr _ (by decide), a, b, c, d]
  rw [WP.block_append_iff]
  refine WP.mono (addOpd_ok s₂) fun s₃ ⟨⟨k, v₃⟩, q₃⟩ => ?_
  have k₃ : Keeps updRegs s s₃ := k₂.trans (q₃.mono (by decide))
  refine WP.mono (stp4_ok (hs.of_keeps k₃ (by decide)) (o := oS) (by decide) _ _ _ _) fun t ht => ⟨⟨k, ?_⟩, ?_,
    fun r hr => by rw [ht]; exact k₃.gpr r hr, by rw [ht]; exact k₃.rd, by rw [ht]; exact k₃.wr, by rw [ht]; exact k₃.sp⟩
  · have hfe : fe t.mem base oS = lo s₃ := by rw [ht]; exact fe_st4 _ _ (by decide) _ _ _ _
    rw [hfe, v₃, l₂, v₂, k₁.mem]
  · rw [ht, ← k₃.mem]; exact st4_outside _ _ (by decide) _ _ _ _

theorem Scr.of_keepRegs' {rs : List Reg} {s t : State} {base : Addr} (hs : Scr s base large)
    (k : KeepRegs rs s t) (h : .x0 ∉ rs) : Scr t base large :=
  ⟨(k.gpr _ h).trans hs.x0, k.wr ▸ hs.wr, hs.nowrap⟩

/-- `f` and `g` after the update. -/
theorem updateFG_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x16 = 0) {U V Q R f' g' : Int}
    (hu : ((s.gpr .x4).toNat : Int) = U + 2 ^ 59) (hv : ((s.gpr .x5).toNat : Int) = V + 2 ^ 59)
    (hq : ((s.gpr .x6).toNat : Int) = Q + 2 ^ 59) (hr : ((s.gpr .x7).toNat : Int) = R + 2 ^ 59)
    (hf : 2 ^ 59 * f' = U * sv (fe s.mem base oF) + V * sv (fe s.mem base oG))
    (hg : 2 ^ 59 * g' = Q * sv (fe s.mem base oF) + R * sv (fe s.mem base oG))
    (bf : |f'| < 2 ^ 255) (bg : |g'| < 2 ^ 255) :
    WP isa (.block updateFG) s fun t =>
      sv (fe t.mem base oF) = f' ∧ sv (fe t.mem base oG) = g' ∧
      (∀ x, (ofs base x < 192 ∨ 256 ≤ ofs base x) ∧ (ofs base x < 320 ∨ 384 ≤ ofs base x) → t.mem x = s.mem x) ∧
      KeepRegs updRegs s t := by
  simp only [updateFG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (sumFG_ok hs) fun s₁ ⟨S₁, o₁, k₁⟩ => ?_
  have hs₁ := Scr.of_keepRegs' hs k₁ (by decide)
  have F₁ : fe s₁.mem base oF = fe s.mem base oF := o₁.fe (by decide) (by decide)
  have G₁ : fe s₁.mem base oG = fe s.mem base oG := o₁.fe (by decide) (by decide)
  rw [← F₁, ← G₁] at S₁ hf hg
  rw [WP.block_append_iff]
  refine WP.mono (rowFG_ok hs₁ (by rw [k₁.gpr _ (by decide), hz]) (Or.inl ⟨rfl, rfl⟩) (o := oT) (by decide)
    (by rw [k₁.gpr _ (by decide)]; exact hu) (by rw [k₁.gpr _ (by decide)]; exact hv) S₁ hf bf)
    fun s₂ ⟨f₂, o₂, k₂'⟩ => ?_
  have k₂ := k₁.trans k₂'
  have hs₂ := Scr.of_keepRegs' hs k₂ (by decide)
  have F₂ : fe s₂.mem base oF = fe s₁.mem base oF := o₂.fe (by decide) (by decide)
  have G₂ : fe s₂.mem base oG = fe s₁.mem base oG := o₂.fe (by decide) (by decide)
  have E₂ : fe s₂.mem base oS = fe s₁.mem base oS := o₂.fe (by decide) (by decide)
  rw [← F₂, ← G₂, ← E₂] at S₁
  rw [← F₂, ← G₂] at hg
  rw [WP.block_append_iff]
  refine WP.mono (rowFG_ok hs₂ (by rw [k₂.gpr _ (by decide), hz]) (Or.inr ⟨rfl, rfl⟩) (o := oG) (by decide)
    (by rw [k₂.gpr _ (by decide)]; exact hq) (by rw [k₂.gpr _ (by decide)]; exact hr) S₁ hg bg)
    fun s₃ ⟨g₃, o₃, k₃'⟩ => ?_
  have k₃ := k₂.trans k₃'
  refine WP.mono (copy4_ok (Scr.of_keepRegs' hs k₃ (by decide)) (d := oF) (o := oT) (by decide) (by decide))
    fun t ⟨f₄, o₄, k₄⟩ => ⟨?_, ?_, fun x hx => ?_, k₃.trans k₄⟩
  · rw [f₄, show fe s₃.mem base oT = fe s₂.mem base oT from o₃.fe (by decide) (by decide), f₂]
  · rw [show fe t.mem base oG = fe s₃.mem base oG from o₄.fe (by decide) (by decide), g₃]
  · rw [o₄ x (by unfold oF; omega_using [hx]), o₃ x (by unfold oG; omega_using [hx]),
      o₂ x (by unfold oT; omega_using [hx]), o₁ x (by unfold oS; omega_using [hx])]

theorem offsetAB_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x16 = 0)
    (hA : fe s.mem base oA < abMax) :
    WP isa (.block offsetAB) s fun t =>
      (∃ k, offE t.mem base + 2 ^ 59 * (fe s.mem base oA + fe s.mem base oB) =
        2 ^ 59 * (2 ^ 256 - 38) + 2 ^ 256 * 2 ^ 64 * k) ∧
      Outside base oE 40 s.mem t.mem ∧ t.gpr .x17 = 19 ∧ KeepRegs updRegs s t := by
  simp only [offsetAB, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldp4_ok hs (o := oA) (by decide) (by decide)) fun s₁ ⟨a, b, c, d, q₁⟩ => ?_
  have k₁ : Keeps updRegs s s₁ := q₁.mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok (hs.of_keeps k₁ (by decide)) (o := oB) (by decide)) fun s₂ ⟨v₂, q₂⟩ => ?_
  have k₂ : Keeps updRegs s s₂ := k₁.trans (q₂.mono (by decide))
  have l₂ : lo s₂ = fe s.mem base oA := by
    unfold lo
    rw [q₂.gpr _ (by decide), q₂.gpr _ (by decide), q₂.gpr _ (by decide), q₂.gpr _ (by decide), a, b, c, d]
  rw [WP.block_append_iff]
  refine WP.mono (twoP_ok s₂ (by rw [k₂.gpr _ (by decide), hz])) fun s₃ ⟨c15, c17, q₃⟩ => ?_
  have k₃ : Keeps updRegs s s₃ := k₂.trans (q₃.mono (by decide))
  have l₃ : lo s₃ = fe s.mem base oA := by
    rw [← l₂]; unfold lo
    rw [q₃.gpr _ (by decide), q₃.gpr _ (by decide), q₃.gpr _ (by decide), q₃.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (negRow_ok s₃ c15 c17 (by rw [l₃]; unfold abMax at hA; omega_using [hA])) fun s₄ ⟨v₄, q₄⟩ => ?_
  have k₄ : Keeps updRegs s s₄ := k₃.trans (q₄.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (subShift_ok s₄ (by rw [k₄.gpr _ (by decide), hz])) fun s₅ ⟨⟨k, v₅⟩, c₅, q₅⟩ => ?_
  have k₅ : Keeps updRegs s s₅ := k₄.trans (q₅.mono (by decide))
  rw [opd_keeps q₄ (by decide), opd_keeps q₃ (by decide), v₂, k₁.mem] at v₅
  rw [l₃] at v₄
  rw [WP.block_append_iff]
  refine WP.mono (stp4_ok (hs.of_keeps k₅ (by decide)) (o := oE) (by decide) _ _ _ _) fun s₆ h₆ => ?_
  have hs₆ : Scr s₆ base large := by rw [h₆]; exact (hs.of_keeps k₅ (by decide)).setMem _
  have hc := workSize_ge large
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    store_sc hs₆ (d := oE + 32) (by decide) (by unfold oE; omega_using [hc]), Option.some.injEq, exists_eq_left']
  have hO : Outside base oE 32 s.mem s₆.mem := by
    rw [h₆, ← k₅.mem]; exact st4_outside _ _ (by decide) _ _ _ _
  have hO' : Outside base oE 40 s.mem (s₆.mem.writeW (off base (oE + 32)) (s₆.gpr .x15)) :=
    (hO.mono (Nat.le_refl _) (by decide)).writeW (by decide) (by decide) (by decide) _
  refine ⟨⟨k, ?_⟩, hO', ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have e : offE (s₆.mem.writeW (off base (oE + 32)) (s₆.gpr .x15)) base = off5 s₅ := by
      unfold offE off5
      rw [word_writeW_self, (writeW_outside s₆.mem base (s₆.gpr .x15) (by decide)).fe (d := oE) (by decide) (by decide), h₆]
      rw [fe_st4 _ _ (by decide)]
      rfl
    rw [e]
    omega_using [v₅, v₄]
  · rw [h₆]; exact c₅
  · rw [h₆]; exact k₅.gpr r hr
  · rw [h₆]; exact k₅.rd
  · rw [h₆]; exact k₅.wr
  · rw [h₆]; exact k₅.sp

/-- `a` and `b` after the update, modulo `p`. -/
theorem updateAB_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x16 = 0) {U V Q R : Int}
    (hu : ((s.gpr .x4).toNat : Int) = U + 2 ^ 59) (hv : ((s.gpr .x5).toNat : Int) = V + 2 ^ 59)
    (hq : ((s.gpr .x6).toNat : Int) = Q + 2 ^ 59) (hr : ((s.gpr .x7).toNat : Int) = R + 2 ^ 59)
    (hUV : |U| + |V| ≤ 2 ^ 59) (hQR : |Q| + |R| ≤ 2 ^ 59)
    (hA : fe s.mem base oA < abMax) (hB : fe s.mem base oB < abMax) :
    WP isa (.block updateAB) s fun t =>
      fe t.mem base oA < abMax ∧ fe t.mem base oB < abMax ∧
      (∃ m : Int, (fe t.mem base oA : Int) = U * fe s.mem base oA + V * fe s.mem base oB + (2 ^ 255 - 19) * m) ∧
      (∃ m : Int, (fe t.mem base oB : Int) = Q * fe s.mem base oA + R * fe s.mem base oB + (2 ^ 255 - 19) * m) ∧
      Outside base 256 168 s.mem t.mem ∧ KeepRegs updRegs s t := by
  simp only [updateAB, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (offsetAB_ok hs hz hA) fun s₁ ⟨E₁, o₁, c₁, k₁⟩ => ?_
  have hs₁ := Scr.of_keepRegs' hs k₁ (by decide)
  have A₁ : fe s₁.mem base oA = fe s.mem base oA := o₁.fe (by decide) (by decide)
  have B₁ : fe s₁.mem base oB = fe s.mem base oB := o₁.fe (by decide) (by decide)
  rw [← A₁, ← B₁] at E₁
  rw [← A₁] at hA
  rw [← B₁] at hB
  rw [WP.block_append_iff]
  refine WP.mono (rowAB_ok hs₁ (by rw [k₁.gpr _ (by decide), hz]) c₁ (Or.inl ⟨rfl, rfl⟩) (o := oT) (by decide)
    (by rw [k₁.gpr _ (by decide)]; exact hu) (by rw [k₁.gpr _ (by decide)]; exact hv) hUV hA hB E₁)
    fun s₂ ⟨l₂, a₂, o₂, c₂, k₂'⟩ => ?_
  have k₂ := k₁.trans k₂'
  have hs₂ := Scr.of_keepRegs' hs k₂ (by decide)
  have A₂ : fe s₂.mem base oA = fe s₁.mem base oA := o₂.fe (by decide) (by decide)
  have B₂ : fe s₂.mem base oB = fe s₁.mem base oB := o₂.fe (by decide) (by decide)
  have E₂ : offE s₂.mem base = offE s₁.mem base := by
    unfold offE; rw [o₂.fe (by decide) (by decide), o₂.word (by decide) (by decide)]
  rw [← A₂, ← B₂, ← E₂] at E₁
  rw [← A₂] at hA
  rw [← B₂] at hB
  rw [WP.block_append_iff]
  refine WP.mono (rowAB_ok hs₂ (by rw [k₂.gpr _ (by decide), hz]) c₂ (Or.inr ⟨rfl, rfl⟩) (o := oB) (by decide)
    (by rw [k₂.gpr _ (by decide)]; exact hq) (by rw [k₂.gpr _ (by decide)]; exact hr) hQR hA hB E₁)
    fun s₃ ⟨l₃, b₃, o₃, _, k₃'⟩ => ?_
  have k₃ := k₂.trans k₃'
  rw [A₂, B₂] at b₃
  rw [A₁, B₁] at b₃ a₂
  have T₃ : fe s₃.mem base oT = fe s₂.mem base oT := o₃.fe (by decide) (by decide)
  refine WP.mono (copy4_ok (Scr.of_keepRegs' hs k₃ (by decide)) (d := oA) (o := oT) (by decide) (by decide))
    fun t ⟨f₄, o₄, k₄⟩ => ?_
  have Bt : fe t.mem base oB = fe s₃.mem base oB := o₄.fe (by decide) (by decide)
  rw [f₄, T₃, Bt]
  exact ⟨l₂, l₃, a₂, b₃, (((o₁.mono (by decide) (by decide)).trans (o₂.mono (by decide) (by decide))).trans
    (o₃.mono (by decide) (by decide))).trans (o₄.mono (by decide) (by decide)), k₃.trans k₄⟩

/-- The matrix biased by `2^59`, and `x16 = 0`. -/
theorem bias_ok (s : State) {u v q r : Int} (hu : s.gpr .x4 = BitVec.ofInt 64 u) (hv : s.gpr .x5 = BitVec.ofInt 64 v)
    (hq : s.gpr .x6 = BitVec.ofInt 64 q) (hr : s.gpr .x7 = BitVec.ofInt 64 r)
    (bu : |u| ≤ 2 ^ 59) (bv : |v| ≤ 2 ^ 59) (bq : |q| ≤ 2 ^ 59) (br : |r| ≤ 2 ^ 59) :
    WP isa (.block bias) s fun t =>
      ((t.gpr .x4).toNat : Int) = u + 2 ^ 59 ∧ ((t.gpr .x5).toNat : Int) = v + 2 ^ 59 ∧
      ((t.gpr .x6).toNat : Int) = q + 2 ^ 59 ∧ ((t.gpr .x7).toNat : Int) = r + 2 ^ 59 ∧
      t.gpr .x16 = 0 ∧ Keeps [.x4, .x5, .x6, .x7, .x16] s t := by
  have key : ∀ w : Int, |w| ≤ 2 ^ 59 →
      (((BitVec.ofInt 64 w + (BitVec.setWidth 64 0x0800#16) <<< 48).toNat : Nat) : Int) = w + 2 ^ 59 := by
    intro w hw
    rw [abs_le] at hw
    rw [show (BitVec.setWidth 64 0x0800#16) <<< 48 = BitVec.ofInt 64 (2 ^ 59) by decide, ← BitVec.ofInt_add,
      BitVec.toNat_ofInt]
    omega_using [hw]
  apply WP.of_runBlock
  simp only [bias, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, show 16 * 0 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    hu, hv, hq, hr,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨key u bu, key v bv, key q bq, key r br, by decide, by row_frame⟩

end VG.Proof.Ed25519.AArch64.Divstep
