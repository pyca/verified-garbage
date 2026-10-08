import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Divstep.State

/-! Loading a divstep batch's input words and its register invariant. -/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- `r = imm`. -/
theorem movzI_ok (s : State) (r : Reg) (imm : BitVec 16) :
    WP isa (.block [.movz .x r imm 0]) s fun t => t.gpr r = imm.setWidth 64 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left', Nat.mul_zero, BitVec.shiftLeft_zero,
    BitVec.setWidth_eq]
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

/-- The slots, from the table area. -/
theorem slots (P : InvCfg) :
    P.L = P.M.n + 1 ∧ P.sF = P.tbl ∧ P.sG = P.tbl + 8 * (P.M.n + 1) ∧ P.sA = P.tbl + 16 * (P.M.n + 1) ∧
      P.sB = P.tbl + 16 * (P.M.n + 1) + 8 * P.M.n ∧ P.sNF = P.tbl + 16 * (P.M.n + 1) + 16 * P.M.n ∧
      P.sNG = P.tbl + 24 * (P.M.n + 1) + 16 * P.M.n ∧ P.sT = P.tbl + 32 * (P.M.n + 1) + 16 * P.M.n := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [InvCfg.L, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sNG, InvCfg.sT] <;> omega

/-- What a batch writes: the slots, `7 n + 6` words. -/
def batchW (P : InvCfg) : List (Nat × Nat) := [(P.tbl, 8 * (7 * P.M.n + 6))]

/-- The batch state in memory: `d` in `x1`, `f`, `g` (two's complement, `n + 1`
words), `a`, `b` (`n` words). -/
structure IInv (P : InvCfg) (base : Addr) (I : Divstep.IState) (s : State) : Prop where
  d : s.gpr .x1 = BitVec.ofInt 64 I.d
  f : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.f % ((2 ^ (64 * P.L) : Nat) : Int)
  g : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.g % ((2 ^ (64 * P.L) : Nat) : Int)
  a : (wordsVal s.mem base P.sA P.M.n : Int) = I.a
  b : (wordsVal s.mem base P.sB P.M.n : Int) = I.b

/-- A batch's start: the counter, `x11 = 1`, `x12 = 0`, the low words of `f`, `g`, the identity. -/
theorem batchStart_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hF : P.sF + 8 ≤ size) (hF8 : P.sF % 8 = 0) (hG : P.sG + 8 ≤ size) (hG8 : P.sG % 8 = 0)
    {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block P.batchStart) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ t.gpr .x11 = 1 ∧ t.gpr .x12 = 0 ∧
      t.gpr .x2 = word s.mem base P.sF ∧ t.gpr .x3 = word s.mem base P.sG ∧
      t.gpr .x4 = 1 ∧ t.gpr .x5 = 0 ∧ t.gpr .x6 = 0 ∧ t.gpr .x7 = 1 ∧ t.mem = s.mem ∧
      KeepRegs [.x2, .x3, .x4, .x5, .x6, .x7, .x11, .x12, .x19] s t := by
  rw [InvCfg.batchStart, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (decCounter_ok s hj hj' h19) fun s₁ ⟨c₁, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₁ .x11 1) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₂ .x12 0) fun s₃ ⟨c₃, k₃⟩ => ?_
  have hs₃ : Scr s₃ base size := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs₃ hF hF8 .x2) fun s₄ ⟨c₄, k₄, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok (hs₃.of_keeps k₄ (by decide)) hG hG8 .x3) fun s₅ ⟨c₅, k₅, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₅ .x4 1) fun s₆ ⟨c₆, k₆⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₆ .x5 0) fun s₇ ⟨c₇, k₇⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₇ .x6 0) fun s₈ ⟨c₈, k₈⟩ => ?_
  refine WP.mono (movzI_ok s₈ .x7 1) fun t ⟨c₉, k₉⟩ => ?_
  have m₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c₉, ?_, ?_⟩
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), c₁]
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), c₂]; rfl
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), c₃]; rfl
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), c₄, m₃]
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide), c₅, k₄.mem, m₃]
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), c₆]; rfl
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), c₇]; rfl
  · rw [k₉.gpr _ (by decide), c₈]; rfl
  · rw [k₉.mem, k₈.mem, k₇.mem, k₆.mem, k₅.mem, k₄.mem, m₃]
  · exact (((((((((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      ((Keeps.regs k₃).mono (by decide))).trans ((Keeps.regs k₄).mono (by decide))).trans
      ((Keeps.regs k₅).mono (by decide))).trans ((Keeps.regs k₆).mono (by decide))).trans
      ((Keeps.regs k₇).mono (by decide))).trans ((Keeps.regs k₈).mono (by decide))).trans
      ((Keeps.regs k₉).mono (by decide))

end VG.Proof.Weierstrass.AArch64
