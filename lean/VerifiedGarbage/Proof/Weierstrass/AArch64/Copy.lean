module

import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Taint

/-!
# Short Weierstrass curves on AArch64: copies, selections and constants

`copy n o a` writes `[a]` to `[o]` (`copy_ok`), `sel n o a b` writes `[a]` or
`[b]` to `[o]` by the mask `x3` (`sel_ok`; `o` may be `a` or `b`), `selPt`
does so for the three coordinates of a point (`selPt_ok`); `setConst n o x`
writes `x` (`setConst_ok`, `SetConst.lean`). Each changes only `[o]` and `x1` (and `x2` for
the selections), and keeps the regions.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- `[o] = [a]`, for `o` at or below `a` or apart from it. -/
theorem copy_ok {size : Nat} : ∀ (n : Nat) {s : State} {base : Addr} {o a : Nat},
    Scr s base size → o + 8 * n ≤ size → a + 8 * n ≤ size → o % 8 = 0 → a % 8 = 0 →
    (o ≤ a ∨ a + 8 * n ≤ o) →
    WP isa (.block (copy n o a)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base a n ∧ KeepRegs [.x1] s s' ∧
      Outside base o (8 * n) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | n + 1, s, base, o, a, hs, ho, ha, ho8, ha8, hsep => by
    have hn := hs.nowrap
    rw [copy, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs (d := a) (by omega_using [ha]) ha8 .x1) fun s₀ ⟨l₀, k₀, _⟩ => ?_
    have hs₀ := hs.of_keeps k₀ (by decide)
    refine WP.mono (st_out hs₀ (o := o) (by omega_using [ho]) ho8 .x1) fun s₁ ⟨m₁, k₁, _⟩ => ?_
    rw [l₀, k₀.mem] at m₁
    have k₀₁ : KeepRegs [.x1] s s₁ := (Keeps.regs k₀).trans (k₁.mono (by simp))
    have hs₁ := hs.of_keepRegs k₀₁ (by decide)
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    have e₁ : wordsVal s₁.mem base (a + 8) n = wordsVal s.mem base (a + 8) n :=
      O₁.wordsVal (by omega_using [hsep]) (by omega_using [ha, hn])
    refine WP.mono (copy_ok n hs₁ (o := o + 8) (a := a + 8) (by omega_using [ho]) (by omega_using [ha]) (by omega_using [ho8])
      (by omega_using [ha8]) (by omega_using [hsep])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    refine ⟨?_, k₀₁.trans k₂, fun x hx => by rw [O₂ x (by omega_using [hx]), O₁ x (by omega_using [hx])]⟩
    rw [wordsVal, O₂.word (by omega_using []) (by omega_using [ho, hn]), m₁, word_writeW_self, e₂, e₁, wordsVal]

/-- `x1 = x1 ^ ((x2 ^ x1) & x3)`, through `x2`. -/
theorem selWord_ok (s : State) :
    WP isa (.block [.logic .eor .x .x2 .x2 .x1, .logic .and .x .x2 .x2 .x3,
        .logic .eor .x .x1 .x1 .x2]) s fun s' =>
      s'.gpr .x1 = s.gpr .x1 ^^^ ((s.gpr .x2 ^^^ s.gpr .x1) &&& s.gpr .x3) ∧ Keeps [.x1, .x2] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `[o] = [b]` if the mask `x3` is all ones (`c`), `[a]` if it is zero; `o`
at or below `a` and `b`, or apart from them. -/
theorem sel_ok {size : Nat} (c : Bool) : ∀ (n : Nat) {s : State} {base : Addr} {o a b : Nat},
    Scr s base size → s.gpr .x3 = (if c then BitVec.allOnes 64 else 0) →
    o + 8 * n ≤ size → a + 8 * n ≤ size → b + 8 * n ≤ size →
    o % 8 = 0 → a % 8 = 0 → b % 8 = 0 →
    (o ≤ a ∨ a + 8 * n ≤ o) → (o ≤ b ∨ b + 8 * n ≤ o) →
    WP isa (.block (sel n o a b)) s fun s' =>
      wordsVal s'.mem base o n = (if c then wordsVal s.mem base b n else wordsVal s.mem base a n) ∧
      KeepRegs [.x1, .x2] s s' ∧ Outside base o (8 * n) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by cases c <;> rfl,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | n + 1, s, base, o, a, b, hs, hc, ho, ha, hb, ho8, ha8, hb8, hsa, hsb => by
    have hn := hs.nowrap
    rw [sel, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs (d := a) (by omega_using [ha]) ha8 .x1) fun s₀ ⟨l₀, k₀, _⟩ => ?_
    have hs₀ := hs.of_keeps k₀ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₀ (d := b) (by omega_using [hb]) hb8 .x2) fun s₁ ⟨l₁, k₁, _⟩ => ?_
    have hs₁ := hs₀.of_keeps k₁ (by decide)
    rw [show ([.logic .eor .x .x2 .x2 .x1, .logic .and .x .x2 .x2 .x3, .logic .eor .x .x1 .x1 .x2,
        st .x1 o] : List Instr) = [.logic .eor .x .x2 .x2 .x1, .logic .and .x .x2 .x2 .x3,
        .logic .eor .x .x1 .x1 .x2] ++ [st .x1 o] from rfl, WP.block_append_iff]
    refine WP.mono (selWord_ok s₁) fun s₂ ⟨v₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    refine WP.mono (st_out hs₂ (o := o) (by omega_using [ho]) ho8 .x1) fun s₃ ⟨m₃, k₃, _⟩ => ?_
    have k₀₃ : KeepRegs [.x1, .x2] s s₃ := (((Keeps.regs k₀).mono (by simp)).trans
      ((Keeps.regs k₁).mono (by simp))).trans (((Keeps.regs k₂).mono (by simp)).trans (k₃.mono (by simp)))
    have hx3 : s₁.gpr .x3 = s.gpr .x3 := by rw [k₁.gpr _ (by decide), k₀.gpr _ (by decide)]
    have h1 : s₁.gpr .x1 = word s.mem base a := by rw [k₁.gpr _ (by decide), l₀]
    rw [v₂, l₁, h1, hx3, hc, sel_word, k₂.mem, k₁.mem, k₀.mem] at m₃
    have hs₃ := hs.of_keepRegs k₀₃ (by decide)
    have O₁ : Outside base o 8 s.mem s₃.mem := by rw [m₃]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    have ea : wordsVal s₃.mem base (a + 8) n = wordsVal s.mem base (a + 8) n :=
      O₁.wordsVal (by omega_using [hsa]) (by omega_using [ha, hn])
    have eb : wordsVal s₃.mem base (b + 8) n = wordsVal s.mem base (b + 8) n :=
      O₁.wordsVal (by omega_using [hsb]) (by omega_using [hb, hn])
    refine WP.mono (sel_ok c n hs₃ (o := o + 8) (a := a + 8) (b := b + 8)
      (by rw [k₀₃.gpr _ (by decide), hc]) (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]) (by omega_using [ho8]) (by omega_using [ha8])
      (by omega_using [hb8]) (by omega_using [hsa]) (by omega_using [hsb])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
    refine ⟨?_, k₀₃.trans k₄, fun x hx => by rw [O₄ x (by omega_using [hx]), O₁ x (by omega_using [hx])]⟩
    rw [wordsVal, O₄.word (by omega_using []) (by omega_using [ho, hn]), m₃, word_writeW_self, e₄, ea, eb]
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true, wordsVal]

/-- `o = b` if the mask `x3` is all ones (`c`), `a` if it is zero, for points
whose slots are in the working space, with `o`'s apart from each other and
from `a`'s and `b`'s. -/
theorem selPt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .x3 = (if c then BitVec.allOnes 64 else 0)) {n : Nat} {o a b : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ size ∧ d % 8 = 0)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o a b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base a.z n) ∧
      KeepRegs [.x1, .x2] s s' ∧
      ∀ x, (ofs base x < o.x ∨ o.x + 8 * n ≤ ofs base x) → (ofs base x < o.y ∨ o.y + 8 * n ≤ ofs base x) →
        (ofs base x < o.z ∨ o.z + 8 * n ≤ ofs base x) → s'.mem x = s.mem x := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨⟨iox, aox⟩, ⟨ioy, aoy⟩, ⟨ioz, aoz⟩, ⟨iax, aax⟩, ⟨iay, aay⟩, ⟨iaz, aaz⟩, ⟨ibx, abx⟩,
    ⟨iby, aby⟩, ⟨ibz, abz⟩⟩ := hin
  obtain ⟨⟨xax, xay, xaz, xbx, xby, xbz⟩, ⟨yax, yay, yaz, ybx, yby, ybz⟩, ⟨zax, zay, zaz, zbx, zby, zbz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  -- `omega` would split every disjunction of the context: give it the facts it needs.
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c n hs hc iox iax ibx aox aax abx (by omega_using [xax])
    (by omega_using [xbx])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c n hs₁ (by rw [k₁.gpr _ (by decide), hc]) ioy iay iby aoy aay aby
    (by omega_using [yay]) (by omega_using [yby])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (sel_ok c n hs₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc]) ioz iaz ibz
    aoz aaz abz (by omega_using [zaz]) (by omega_using [zbz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, fun x h₁ h₂ h₃ => by rw [O₃ x h₃, O₂ x h₂, O₁ x h₁]⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := b.y) (by omega_using [xby]) (by omega_using [iby, hn]),
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := b.z) (by omega_using [ybz]) (by omega_using [ibz, hn]),
      O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := b.z) (by omega_using [xbz]) (by omega_using [ibz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]

end VG.Proof.Weierstrass.AArch64
