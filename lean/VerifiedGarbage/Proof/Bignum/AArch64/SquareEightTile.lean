module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTriRow
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The row-wise triangle of an eight-limb square

The cross products `Σ_{i<j<8} a_i a_j 2^(64(i+j))` of eight words at
`x8`, written as fifteen words at `x16` (word 0, zero before, is not
written): rows 1 to 7 (`triRow_ok`), each storing its first word, then the
accumulators' words 8 to 14. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEight
open VG.Proof.MlKem.AArch64 (Keep)

abbrev codeRegs : List Reg := inputs ++ work

/-- After the rows before row `j`: the words `0 … j - 1` in memory and the
words `j … 2j - 2` in the accumulators make the cross products of the first
`j` inputs. -/
def TriInv (m0 : Mem) (B : Addr) (eA eT : Nat) (s0 : State) (j : Nat) (t : State) : Prop :=
  wv t.mem B eT j + 2 ^ (64 * j) * win t j (j - 1) = Square.crossValue m0 B eA j ∧
  Outside B (eT + 8) (8 * (j - 1)) s0.mem t.mem ∧ Keep work s0 t

theorem triRows_ok {s0 : State} {B : Addr} {Z eA eT : Nat} (n : Nat) (hn : n ≤ 7)
    (hs : Scr s0 B Z) (h16 : s0.gpr .x16 = off B eT) (hT : eT + 120 ≤ Z) (h7 : s0.gpr .x7 = 0)
    (hin : ∀ i < 8, s0.gpr (inp i) = word s0.mem B (eA + 8 * i))
    (hz : wv s0.mem B eT 1 = 0) :
    WP isa (.block ((List.range n).flatMap fun j => row (j + 1))) s0 (TriInv s0.mem B eA eT s0 (n + 1)) := by
  induction n with
  | zero =>
    refine WP.block_nil ⟨?_, Outside.refl _ _ _ _, Keep.refl _ _⟩
    simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, Nat.add_zero, win, regVal, Square.value]
    rw [hz]
    simp [Square.crossValue, Square.cross, Square.value]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine WP.mono (ih (by omega_arith)) fun t ⟨hv, ho, kt⟩ => ?_
    have hn1 : n + 1 - 1 = n := by omega_arith
    have hin' : ∀ i < 8, t.gpr (inp i) = word s0.mem B (eA + 8 * i) :=
      fun i hi => (kt.gpr _ (inp_not_work i hi)).trans (hin i hi)
    have hval : regVal t inp (n + 1) = wv s0.mem B eA (n + 1) :=
      inputs_value (s := t) (fun i hi => hin' i (by omega_arith))
    have haj : t.gpr (inp (n + 1)) = word s0.mem B (eA + 8 * (n + 1)) := hin' _ (by omega_arith)
    have hcross := Square.crossValue_succ s0.mem B eA (n + 1)
    have hlt := cross_words_succ_lt s0.mem B eA (n + 1)
    rw [hn1] at hv
    have hb : win t (n + 1) n + (t.gpr (inp (n + 1))).toNat * regVal t inp (n + 1) <
        2 ^ (64 * (n + 1 + 1)) := by
      rw [hval, haj]
      have e : wv t.mem B eT (n + 1) + 2 ^ (64 * (n + 1)) *
          (win t (n + 1) n + (word s0.mem B (eA + 8 * (n + 1))).toNat * wv s0.mem B eA (n + 1)) =
          Square.crossValue s0.mem B eA (n + 1 + 1) := by
        rw [hcross, ← hv, Nat.mul_add]; grind
      have hp : 2 ^ (64 * (2 * (n + 1) + 1)) = 2 ^ (64 * (n + 1)) * 2 ^ (64 * (n + 1 + 1)) := by
        rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega_arith)
      rw [hp] at hlt
      exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (e ▸ hlt))
    refine WP.mono (triRow_ok (j := n + 1) (by omega_arith) (by omega_arith) (hs.congr kt.wr)
      ((kt.gpr _ x16_not_work).trans h16) (by omega_arith) ((kt.gpr _ x7_not_work).trans h7)
      (by rw [hn1]; exact hb)) fun u ⟨⟨hu, hum⟩, ku⟩ => ?_
    rw [hn1] at hu
    have hnw : (eT + 8 * (n + 1)) + 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega_arith
    refine ⟨?_, ?_, kt.trans ku |>.mono fun r hr => by
      rcases List.mem_append.mp hr with h | h <;> exact h⟩
    · have hw := wv_writeW_top t.mem B eT (n + 1) (u.gpr (acc (n + 1))) (by omega_arith)
      rw [hum, show n + 1 + 1 - 1 = n + 1 by omega_arith, hw]
      have hs2 := win_split u (n + 1) (n + 1)
      rw [hu] at hs2
      rw [hval, haj] at hs2
      rw [hcross, ← hv]
      rw [show 2 ^ (64 * (n + 1 + 1)) = 2 ^ (64 * (n + 1)) * 2 ^ 64 by
        rw [← Nat.pow_add, Nat.mul_succ]]
      grind
    · rw [hum]
      have hw := writeW_outside t.mem B (u.gpr (acc (n + 1))) (d := eT + 8 * (n + 1)) hnw
      exact (ho.mono (by omega_arith) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))

/-- The accumulators' words `w … w + k - 1` stored after the words before
them (`w = 8`; a variable, so that no tactic evaluates `2 ^ (64 * 8)`). -/
theorem stores_ok {s : State} {B : Addr} {Z eT w : Nat} (hw : w = 8) (k : Nat) (hk : k ≤ 7)
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 120 ≤ Z) :
    WP isa (.block ((List.range k).map fun i => st (acc (i + 8)) .x16 (8 * (i + 8)))) s fun t =>
      (wv t.mem B eT (w + k) = wv s.mem B eT w + 2 ^ (64 * w) * win s w k ∧
        Outside B (eT + 8 * w) (8 * k) s.mem t.mem) ∧ Keep [] s t := by
  induction k with
  | zero =>
    refine WP.block_nil ⟨⟨?_, Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
    rw [show win s w 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    apply WP.block_append
    refine WP.mono (ih (by omega_arith)) fun t ⟨⟨hv, ho⟩, kt⟩ => ?_
    refine WP.mono (storeWord_ok (acc (k + 8)) (k + 8) (hs.congr kt.wr) ((kt.gpr _ (by simp)).trans h16)
      (by omega_arith) (by omega_arith)) fun u ⟨hum, ku⟩ => ?_
    have hnw : (eT + 8 * (k + 8)) + 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega_arith
    refine ⟨⟨?_, ?_⟩, (kt.trans ku).mono (by simp)⟩
    · have hwt := wv_writeW_top t.mem B eT (w + k) (t.gpr (acc (k + 8))) (by omega_arith)
      rw [hum, show eT + 8 * (k + 8) = eT + 8 * (w + k) by omega_arith, show w + (k + 1) = w + k + 1 by omega_arith,
        hwt, hv, win_succ, kt.gpr _ (by simp), show w + k = k + 8 by omega_arith, Nat.mul_add 64 k 8,
        ← hw, Nat.pow_add, ← Nat.pow_mul]
      generalize 2 ^ (64 * w) = P
      generalize 2 ^ (64 * k) = Q
      grind
    · rw [hum]
      have hwo := writeW_outside t.mem B (t.gpr (acc (k + 8))) (d := eT + 8 * (k + 8)) hnw
      exact (ho.mono (by omega_arith) (by omega_arith)).trans (hwo.mono (by omega_arith) (by omega_arith))

/-- The scheduled eight-limb triangular product, including input loads,
every carry, and the final output words. -/
theorem code_ok {s : State} {B : Addr} {Z eA eT : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA) (h16 : s.gpr .x16 = off B eT)
    (hA : eA + 64 ≤ Z) (hT : eT + 120 ≤ Z) (h7 : s.gpr .x7 = 0)
    (hz : wv s.mem B eT 1 = 0) :
    WP isa (.block code) s fun t =>
      wv t.mem B eT 15 = Square.crossValue s.mem B eA 8 ∧
        Outside B (eT + 8) 112 s.mem t.mem ∧ Keep codeRegs s t := by
  unfold code
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (loadInputs_ok hs h8 hA) fun a ⟨⟨hai, ham⟩, ka⟩ => ?_
  have h16a : a.gpr .x16 = off B eT := (ka.gpr _ (by decide)).trans h16
  have h7a : a.gpr .x7 = 0 := (ka.gpr _ (by decide)).trans h7
  apply WP.block_append
  refine WP.mono (triRows_ok (eA := eA) 7 (Nat.le_refl _) (hs.congr ka.wr) h16a hT h7a
    (fun i hi => (hai i hi).trans (by rw [ham])) (by rw [ham]; exact hz)) fun b ⟨hbv, hbo, kb⟩ => ?_
  refine WP.mono (stores_ok (w := 8) rfl 7 (Nat.le_refl _) (hs.congr (kb.wr.trans ka.wr))
    ((kb.gpr _ x16_not_work).trans h16a) hT) fun t ⟨⟨htv, hto⟩, kt⟩ => ?_
  refine ⟨?_, ?_, ((ka.trans kb).trans kt).mono fun r hr => by rwa [List.append_nil] at hr⟩
  · rw [htv]
    rw [ham, show (7 : Nat) + 1 - 1 = 7 from rfl, show (7 : Nat) + 1 = 8 from rfl] at hbv
    exact hbv
  · rw [← ham]
    exact (hbo.mono (by omega_arith) (by omega_arith)).trans (hto.mono (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.AArch64.SquareEight
