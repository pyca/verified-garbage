module
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce

/-!
# ML-KEM's 16-bit NTT on AArch64: tables of halfwords

`halves H r off` (`Impl/MlKem/AArch64/Ntt16.lean`) stores the halfwords `H`
at `[r + off]`, four at a time: each group of four is a doubleword built by
`movz` and three `movk` (`pack4`), stored by `str` (`halves_ok`). A vector
loaded from the table has the halfwords as its lanes (`vhalf_table`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 Impl.MlKem.AArch64.Ntt16

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movk {d : Reg} {imm : BitVec 16} {hw : Nat} (h : hw < 4)
    (k : ∀ s', Only [d] s s' →
      s'.gpr d = (s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw)) ||| imm.setWidth 64 <<< (16 * hw)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.movk .x d imm hw :: is)) s Q :=
  wp_x (by simp only [exec, State.read, Size.bits, BitVec.setWidth_eq, show 16 * hw < 64 by omega,
    ite_true]) k

end

/-- `movz` and three `movk` of `a`, `b`, `c`, `d`: the doubleword `d c b a`. -/
theorem pack4 (a b c d : BitVec 16) :
    ((((a.setWidth 64 &&& ~~~((0xFFFF : BitVec 64) <<< (16 * 1))) ||| b.setWidth 64 <<< (16 * 1)) &&&
        ~~~((0xFFFF : BitVec 64) <<< (16 * 2)) ||| c.setWidth 64 <<< (16 * 2)) &&&
        ~~~((0xFFFF : BitVec 64) <<< (16 * 3)) ||| d.setWidth 64 <<< (16 * 3)) = d ++ c ++ b ++ a := by
  have m : ∀ i < 64, ∀ k < 4, ((0xFFFF : BitVec 64) <<< (16 * k)).getLsbD i =
      decide (16 * k ≤ i ∧ i < 16 * k + 16) := by decide
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, m i hi 1 (by decide),
    m i hi 2 (by decide), m i hi 3 (by decide), BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  have ge : ∀ (x : BitVec 16) (j : Nat), 16 ≤ j → x.getLsbD j = false := fun x j h =>
    BitVec.getLsbD_of_ge x j h
  rcases (by omega : i < 16 ∨ (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48) ∨ 48 ≤ i) with h | h | h | h <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, ge, Bool.and_true, Bool.true_and,
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false,
      ite_eq_left, ite_eq_right, Nat.sub_sub] <;>
    exact congrArg _ (by omega)

/-- The four halfwords of group `j` of `H`, as a doubleword. -/
def hw4 (H : List Nat) (j : Nat) : BitVec 64 :=
  BitVec.ofNat 16 (H.getD (4 * j + 3) 0) ++ BitVec.ofNat 16 (H.getD (4 * j + 2) 0) ++
    BitVec.ofNat 16 (H.getD (4 * j + 1) 0) ++ BitVec.ofNat 16 (H.getD (4 * j) 0)

/-- After the first `g` groups of `halves H r off`, with `r` pointing to a region of 1024 bytes. -/
structure HInv (H : List Nat) (r : Reg) (off : Nat) (s₀ : State) (g : Nat) (s : State) : Prop where
  keep : Keep [.x9] s₀ s
  frame : Frame [⟨s₀.gpr r, 1024⟩] s₀.mem s.mem
  tab : ∀ j < g, s.mem.readW (s₀.gpr r + BitVec.ofNat 64 (off + 8 * j)) 64 = hw4 H j

theorem halves_ok (H : List Nat) {r : Reg} (hr : r ≠ .x9) {off : Nat}
    (hoff : off + 2 * H.length ≤ 1024) (ho : off % 8 = 0) {s₀ : State}
    (hreg : ⟨s₀.gpr r, 1024⟩ ∈ s₀.wr) :
    WP isa (.block (halves H r off)) s₀ (HInv H r off s₀ (H.length / 4)) := by
  refine wp_range_flatMap (M := isa) (HInv H r off s₀) (fun g s hg h => ?_) _ (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hrk : s.gpr r = s₀.gpr r := h.keep.get r (not_mem_one hr)
  have ha : off + 8 * g + 8 ≤ 1024 := by omega
  refine wp_movz fun s₁ h₁ e₁ => wp_movk (by decide) fun s₂ h₂ e₂ => wp_movk (by decide) fun s₃ h₃ e₃ =>
    wp_movk (by decide) fun s₄ h₄ e₄ => wp_strx (a := s₀.gpr r + BitVec.ofNat 64 (off + 8 * g))
      ⟨by omega, by omega⟩ (by rw [h₄.gpr _ (not_mem_one hr), h₃.gpr _ (not_mem_one hr),
        h₂.gpr _ (not_mem_one hr), h₁.gpr _ (not_mem_one hr), hrk])
      (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, h.keep.wr]
          exact in_regions hreg (contains_off (by omega) (by decide))) fun s₅ h₅ => wp_nil ?_
  have v : s₄.gpr .x9 = hw4 H g := by
    rw [e₄, h₃.gpr .x9 |> fun _ => e₃, e₂, e₁]
    exact pack4 _ _ _ _
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨(h.keep.trans ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep)).mono,
    ?_, fun j hj => ?_⟩
  · rw [h₅.mem, m₄]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))
  · rw [h₅.mem, m₄, v]
    by_cases e : j = g
    · subst e; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab j (by omega)

/-- A 16-byte load as two doublewords. -/
theorem read16_dw (m : Mem) (a : Addr) :
    m.read a 16 = ofVDwords (m.readW a 64) (m.readW (a + BitVec.ofNat 64 8) 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_read m 16 a i (by omega)]
  simp only [ofVDwords, BitVec.getLsbD_append, Mem.readW, BitVec.getLsbD_setWidth]
  by_cases h : i < 64
  · rw [ite_eq_left h, getLsbD_read m 8 a i (by omega)]; simp [h]
  · rw [ite_eq_right h, getLsbD_read m 8 _ (i - 64) (by omega)]
    simp only [show i - 64 < 64 by omega, decide_true, Bool.true_and]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 + (i - 64) / 8 = i / 8 by omega,
      show (i - 64) % 8 = i % 8 by omega]

theorem hw4_half (H : List Nat) (j : Nat) {h : Nat} (hh : h < 4) :
    (hw4 H j).extractLsb' (16 * h) 16 = BitVec.ofNat 16 (H.getD (4 * j + h) 0) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [hw4, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  match h, hh with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_zero]
    all_goals exact congrArg _ (by omega)

/-- Lane `e` of the vector `i` of a table of halfwords. -/
theorem vhalf_table {m : Mem} {p : Addr} {off N : Nat} {H : List Nat}
    (htab : ∀ j < N, m.readW (p + BitVec.ofNat 64 (off + 8 * j)) 64 = hw4 H j) {i : Nat}
    (hi : 2 * i + 1 < N) {e : Nat} (he : e < 8) :
    vhalf (m.read (p + BitVec.ofNat 64 (off + 16 * i)) 16) e = BitVec.ofNat 16 (H.getD (8 * i + e) 0) := by
  rw [read16_dw, BitVec.add_assoc, ← BitVec.ofNat_add,
    show off + 16 * i + 8 = off + 8 * (2 * i + 1) by omega,
    show off + 16 * i = off + 8 * (2 * i) by omega, htab _ (by omega), htab _ hi,
    vhalf_ofVDwords _ _ he]
  by_cases h : e < 4
  · rw [ite_eq_left h, hw4_half _ _ (by omega)]
    exact congrArg (BitVec.ofNat 16) (congrArg (fun k => H.getD k 0) (by omega))
  · rw [ite_eq_right h, hw4_half _ _ (by omega)]
    exact congrArg (BitVec.ofNat 16) (congrArg (fun k => H.getD k 0) (by omega))

end VG.Proof.MlKem.AArch64.Ntt16
