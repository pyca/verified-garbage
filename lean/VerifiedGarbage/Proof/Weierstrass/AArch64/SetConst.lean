module

public import VerifiedGarbage.Impl.Weierstrass.AArch64
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# Short Weierstrass curves on AArch64: constants

`setConst n o x` writes `x` to `[o]` (`setConst_ok`), changing only `[o]`
and `x1`, and keeping the regions; the Montgomery products' functions
(`MontFnG.lean`) write their modulus with it.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- `[o] = t`, as `Outside` and the word written. -/
theorem st_out {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o : Nat}
    (ho : o + 8 ≤ size) (ho8 : o % 8 = 0) (t : Reg) :
    WP isa (.block [st t o]) s fun s' => s'.mem = s.mem.writeW (off base o) (s.gpr t) ∧
      KeepRegs [] s s' ∧ s'.gpr = s.gpr :=
  WP.mono (st_ok hs ho ho8 t) fun s' e => by subst e; exact ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl⟩

/-! ## Constants -/

/-- One word of `setConst`. -/
def constStep (o x j : Nat) : List Instr :=
  const64 .x1 (BitVec.ofNat 64 (x >>> (64 * j))) ++ [st .x1 (o + 8 * j)]

theorem setConst_eq (n o x : Nat) : setConst n o x = (List.range n).flatMap (constStep o x) := rfl

theorem constSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o x : Nat}
    (ho8 : o % 8 = 0) : ∀ k, o + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (constStep o x))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = BitVec.ofNat 64 (x >>> (64 * j))) ∧
      KeepRegs [.x1] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (constSteps_ok hs ho8 k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [constStep, WP.block_append_iff]
    refine WP.mono (const64_ok s₁ .x1 _) fun s₂ ⟨v₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    refine WP.mono (st_out hs₂ (o := o + 8 * k) (by omega) (by omega) .x1) fun s₃ ⟨m₃, k₃, _⟩ => ?_
    rw [v₂, k₂.mem] at m₃
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₃.mem := by
      rw [m₃]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, (k₁.trans ((Keeps.regs k₂).trans (k₃.mono (by simp)))),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₃, word_writeW_self]

/-- `[o] = x`. -/
theorem setConst_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o x : Nat}
    (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (hx : x < 2 ^ (64 * n)) :
    WP isa (.block (setConst n o x)) s fun s' =>
      wordsVal s'.mem base o n = x ∧ KeepRegs [.x1] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [setConst_eq]
  exact WP.mono (constSteps_ok hs ho8 n ho) fun s' ⟨e, k, O⟩ =>
    ⟨wordsVal_of_shifts _ _ o n x hx e, k, O⟩

end VG.Proof.Weierstrass.AArch64
