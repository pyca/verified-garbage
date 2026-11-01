module
public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Divstep.PackedDef
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Inv
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step

import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Divstep.PackedShl
import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Data.Finset.Attr
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-!
# Inversion by divsteps on AArch64: packed divsteps

A packed step's block computes `Proof/Divstep/PackedDef.lean`'s `pstep`
(`pstepCode_ok`) when the `g` row's bits below the step's are zero, as they
are in a chunk (`Divstep.psteps_shl`), and a chunk's steps its `psteps`
(`pstepsCode_ok`). A chunk (`pchunk_ok`) starts the rows from the low words
of `f` and `g` in `x2`, `x3`, runs its steps, takes the matrix from the rows
(`pext_ok`), updates the low words by it (`plow_ok`) and multiplies the
batch's matrix by it (`pcomp_ok`); as integers, the batch so far is `msteps`
from the batch's start (`Divstep.psteps_rel`, `pext_rel`, `low_upd`,
`msteps_gen`). Its `59` steps in chunks leave the batch's `d` and matrix
(`pwords_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Divstep (MSt mstep msteps pstep pextLo pextHi ite_t ite_f)

/-! ## A step -/

/-- The registers a chunk's steps write. -/
abbrev pRegs : List Reg := [.x1, .x8, .x9, .x10, .x11, .x12, .x13, .x16]

/-- A packed step's block, for each kind of step: `odd` is the mask's test,
`neg` the sign bit of `~d`. -/
theorem pstepCode_run (s : State) {g t : Reg} (hg : g = .x9 ∧ t = .x10 ∨ g = .x10 ∧ t = .x9)
    {odd neg : Bool} (hz : decide (s.gpr g &&& s.gpr .x12 = 0) = !odd) (hn : (s.gpr .x1).msb = neg) :
    WP isa (.block (pstepCode g t)) s fun s' =>
      s'.gpr .x1 = (if odd && neg then -(s.gpr .x1 + 4) else s.gpr .x1 - 2) ∧
      s'.gpr .x8 = (if odd && neg then s.gpr g + s.gpr g else s.gpr .x8 + s.gpr .x8) ∧
      s'.gpr t = (if odd && neg then s.gpr g - s.gpr .x8 else if odd then s.gpr g + s.gpr .x8 else s.gpr g) ∧
      s'.gpr .x12 = s.gpr .x12 + s.gpr .x12 ∧ Keeps [.x1, .x8, .x11, .x12, .x13, .x16, t] s s' := by
  apply WP.of_runBlock
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases odd <;>
  · simp only [pstepCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', CondCode.holds,
      State.flagsAdd, hz, Bool.toNat_true, one64, add_not0_one', hn, show (4 : Nat) < 4096 from by decide,
      show (2 : Nat) < 4096 from by decide, show (0 : Nat) < 32 ∧ (0 : Nat) < 16 from by decide, and_self,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
      show Nat.testBit 0 3 = false by decide, RegUpd.nf_write, RegUpd.zf_write, Bool.false_eq_true]
    refine ⟨by cases neg <;> rfl, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    simp only [RegUpd.gpr_write, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

/-- Bit `j` of `G` by the mask `2^j`. -/
theorem and_mask_iff (G : BitVec 64) {j : Nat} (hj : j < 64) :
    G &&& BitVec.ofNat 64 (2 ^ j) = 0 ↔ G.getLsbD j = false := by
  constructor
  · intro h
    have := congrArg (fun x => x.getLsbD j) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_self] at this
    simpa [hj] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
    by_cases e : j = i
    · subst e; simp [h]
    · simp [e]

/-- Bit `63` of `G << (63 - j)` is bit `j` of `G`. -/
theorem shl_getLsbD (G : BitVec 64) {j : Nat} (hj : j ≤ 63) : (G <<< (63 - j)).getLsbD 63 = G.getLsbD j := by
  rw [BitVec.getLsbD_shiftLeft, Nat.sub_sub_self hj]
  simp only [show (63 : Nat) < 64 from by decide, decide_true, Bool.true_and,
    show ¬ (63 : Nat) < 63 - j from by omega_arith, decide_false, Bool.not_false]

theorem negE (E : BitVec 64) : -(E + 4) = -2 - E - 2 := by grind

/-- Divstep `j` of a chunk, its `g` row's bits below `j` zero: `pstep`. -/
theorem pstepCode_ok (s : State) {j : Nat} (hj : j ≤ 62) {g t : Reg}
    (hg : g = .x9 ∧ t = .x10 ∨ g = .x10 ∧ t = .x9) (hm : s.gpr .x12 = BitVec.ofNat 64 (2 ^ j))
    (hsh : (s.gpr g <<< (63 - j)).toNat = 0 ∨ (s.gpr g <<< (63 - j)).toNat = 2 ^ 63) :
    WP isa (.block (pstepCode g t)) s fun s' =>
      (s'.gpr .x1, s'.gpr .x8, s'.gpr t) = pstep j (s.gpr .x1, s.gpr .x8, s.gpr g) ∧
      s'.gpr .x12 = BitVec.ofNat 64 (2 ^ (j + 1)) ∧ Keeps [.x1, .x8, .x11, .x12, .x13, .x16, t] s s' := by
  obtain ⟨E, hE⟩ : ∃ E, s.gpr .x1 = E := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, s.gpr .x8 = F := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, s.gpr g = G := ⟨_, rfl⟩
  rw [hG] at hsh
  have hbit := and_mask_iff G (j := j) (by omega_arith)
  have hsb := shl_getLsbD G (j := j) (by omega_arith)
  have hmsb : E.msb = decide (2 ^ 63 ≤ E.toNat) := BitVec.msb_eq_decide E
  have hlt := E.isLt
  have m2 : s.gpr .x12 + s.gpr .x12 = BitVec.ofNat 64 (2 ^ (j + 1)) := by
    rw [hm, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]
  rw [hE, hF, hG]
  unfold pstep
  simp only
  rcases hsh with h0 | h1
  · have hz : G <<< (63 - j) = 0 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
    have hb : G.getLsbD j = false := by rw [← hsb, hz]; simp
    refine WP.mono (pstepCode_run s hg (odd := false) (neg := E.msb)
      (by rw [hm, hG, decide_eq_true (hbit.mpr hb)]; rfl) (by rw [hE])) fun s' ⟨e1, e8, et, e12, k⟩ => ?_
    rw [ite_f (by rw [h0]; omega_arith), ite_t hz]
    refine ⟨?_, by rw [e12, m2], k⟩
    simp only [e1, e8, et, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hE, hF, hG]
  · have hz : ¬ G <<< (63 - j) = 0 := fun h => by rw [h] at h1; simp at h1
    have hb : G.getLsbD j = true := by
      rw [← hsb, ← BitVec.testBit_toNat, h1]; exact Nat.testBit_two_pow_self
    have hnz : ¬ G &&& BitVec.ofNat 64 (2 ^ j) = 0 := fun h => by rw [hbit.mp h] at hb; exact absurd hb (by decide)
    refine WP.mono (pstepCode_run s hg (odd := true) (neg := E.msb)
      (by rw [hm, hG, decide_eq_false hnz]; rfl) (by rw [hE])) fun s' ⟨e1, e8, et, e12, k⟩ => ?_
    refine ⟨?_, by rw [e12, m2], k⟩
    cases hn : E.msb
    · rw [hn] at hmsb
      have : ¬ 2 ^ 63 ≤ E.toNat := fun h => by rw [decide_eq_true h] at hmsb; exact absurd hmsb (by decide)
      rw [ite_f (by rw [h1]; omega_arith), ite_f hz]
      simp only [e1, e8, et, hn, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hE, hF, hG]
    · rw [hn] at hmsb
      have : 2 ^ 63 ≤ E.toNat := of_decide_eq_true hmsb.symm
      rw [ite_t (by rw [h1]; omega_arith)]
      simp only [e1, e8, et, hn, Bool.and_self, ↓reduceIte, hE, hF, hG, negE]

theorem gReg_cases (j : Nat) : gReg j = .x9 ∧ gReg (j + 1) = .x10 ∨ gReg j = .x10 ∧ gReg (j + 1) = .x9 := by
  unfold gReg
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · left; exact ⟨ite_t h, ite_f (by omega_arith)⟩
  · right; exact ⟨ite_f (by omega_arith), ite_t (by omega_arith)⟩

theorem gReg_mem (j : Nat) : gReg j ∈ pRegs := by
  rcases gReg_cases j with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide

/-- Steps `0 … n - 1` of a chunk of `N`, from the mask `1`, the `g` row's
bits below each step's zero. -/
theorem pstepsList_ok (s : State) {N : Nat} (hN : N ≤ 62) (hm : s.gpr .x12 = 1)
    (hsh : ∀ k < N, ((Divstep.psteps k (s.gpr .x1, s.gpr .x8, s.gpr .x9)).2.2 <<< (63 - k)).toNat = 0 ∨
      ((Divstep.psteps k (s.gpr .x1, s.gpr .x8, s.gpr .x9)).2.2 <<< (63 - k)).toNat = 2 ^ 63) :
    ∀ n ≤ N, WP isa (.block ((List.range n).flatMap fun j => pstepCode (gReg j) (gReg (j + 1)))) s fun s' =>
      (s'.gpr .x1, s'.gpr .x8, s'.gpr (gReg n)) = Divstep.psteps n (s.gpr .x1, s.gpr .x8, s.gpr .x9) ∧
      s'.gpr .x12 = BitVec.ofNat 64 (2 ^ n) ∧ Keeps pRegs s s'
  | 0, _ => WP.block_nil_iff.mpr ⟨rfl, by rw [hm]; rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (pstepsList_ok s hN hm hsh n (by omega_arith)) fun s₁ ⟨e₁, m₁, k₁⟩ => ?_
    have hs := hsh n (by omega_arith)
    rw [← e₁] at hs
    refine WP.mono (pstepCode_ok s₁ (j := n) (by omega_arith) (gReg_cases n) m₁ hs) fun s₂ ⟨e₂, m₂, k₂⟩ =>
      ⟨by rw [e₂, Divstep.psteps, ← e₁], m₂, k₁.trans (k₂.mono ?_)⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | decide | exact gReg_mem _

/-- A chunk's `n ≤ 15` steps. -/
theorem pstepsCode_ok (s : State) {n : Nat} (hn : n ≤ 15) (hm : s.gpr .x12 = 1)
    (hsh : ∀ k < n, ((Divstep.psteps k (s.gpr .x1, s.gpr .x8, s.gpr .x9)).2.2 <<< (63 - k)).toNat = 0 ∨
      ((Divstep.psteps k (s.gpr .x1, s.gpr .x8, s.gpr .x9)).2.2 <<< (63 - k)).toNat = 2 ^ 63) :
    WP isa (.block (pstepsCode n)) s fun s' =>
      (s'.gpr .x1, s'.gpr .x8, s'.gpr (gReg n)) = Divstep.psteps n (s.gpr .x1, s.gpr .x8, s.gpr .x9) ∧
      Keeps pRegs s s' :=
  WP.mono (pstepsList_ok s (N := n) (by omega_arith) hm hsh n le_rfl) fun _ ⟨e, _, k⟩ => ⟨e, k⟩

/-! ## A chunk's rows and matrix -/

/-- The rows' start. -/
theorem pset_ok (s : State) :
    WP isa (.block pset) s fun s' =>
      s'.gpr .x8 = (s.gpr .x2 &&& 0x7fff) + 2 ^ 31 ∧ s'.gpr .x9 = (s.gpr .x3 &&& 0x7fff) + 2 ^ 47 ∧
      s'.gpr .x12 = 1 ∧ Keeps [.x8, .x9, .x12, .x13, .x16] s s' := by
  apply WP.of_runBlock
  simp only [pset, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide]
  refine ⟨congrArg₂ (· + ·) (congrArg (s.gpr .x2 &&& ·) (by decide)) (by decide),
    congrArg₂ (· + ·) (congrArg (s.gpr .x3 &&& ·) (by decide)) (by decide), by decide,
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5⟩ := hr
  simp only [RegUpd.gpr_write, h1, h2, h3, h4, h5, ↓reduceIte]

/-- A row's start as an integer: the low 15 bits, plus a constant. -/
theorem pset_int (w c : BitVec 64) {C : Int} (hc : c = BitVec.ofInt 64 C) :
    (w &&& 0x7fff) + c = BitVec.ofInt 64 (((w.toNat % 2 ^ 15 : Nat) : Int) + C) := by
  have h : (w &&& 0x7fff) = BitVec.ofNat 64 (w.toNat % 2 ^ 15) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (0x7fff : BitVec 64).toNat = 2 ^ 15 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
  rw [h, hc, BitVec.ofInt_add, BitVec.ofInt_natCast]

theorem c31 : (2 ^ 31 : BitVec 64) = BitVec.ofInt 64 (2 ^ 31) := by decide
theorem c47 : (2 ^ 47 : BitVec 64) = BitVec.ofInt 64 (2 ^ 47) := by decide

/-- The registers `pext`, `plow` and `pcomp` see as distinct, for the `g` rows. -/
theorem gpair_ne {g g' : Reg} (hg : g = .x9 ∧ g' = .x10 ∨ g = .x10 ∧ g' = .x9) :
    ∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x11, .x12, .x13, .x16, .x17],
      (¬ r = g ∧ ¬ g = r) ∧ (¬ r = g' ∧ ¬ g' = r) := by
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- The constants of `pext`. -/
theorem pextK_ok (s : State) :
    WP isa (.block pextK) s fun s' =>
      s'.gpr .x13 = Divstep.pextC ∧ s'.gpr .x17 = 16384 ∧ Keeps [.x13, .x17] s s' := by
  apply WP.of_runBlock
  simp only [pextK, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide]
  refine ⟨by decide, by decide, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ↓reduceIte]

/-- The matrix from the rows. -/
theorem pext_ok (s : State) {g g' : Reg} (hg : g = .x9 ∧ g' = .x10 ∨ g = .x10 ∧ g' = .x9) :
    WP isa (.block (pext g g')) s fun s' =>
      s'.gpr .x8 = pextLo (s.gpr .x8) ∧ s'.gpr .x11 = pextHi (s.gpr .x8) ∧
      s'.gpr g = pextLo (s.gpr g) ∧ s'.gpr g' = pextHi (s.gpr g) ∧
      Keeps [.x8, .x11, .x13, .x17, g, g'] s s' := by
  rw [pext, WP.block_append_iff]
  refine WP.mono (pextK_ok s) fun s₁ ⟨c13, c17, k₁⟩ => ?_
  have e8 : s₁.gpr .x8 = s.gpr .x8 := k₁.gpr _ (by decide)
  have e9 : s₁.gpr .x9 = s.gpr .x9 := k₁.gpr _ (by decide)
  have e10 : s₁.gpr .x10 = s.gpr .x10 := k₁.gpr _ (by decide)
  apply WP.of_runBlock
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
      show 47 < Size.x.bits from by decide, show 17 < Size.x.bits from by decide,
      show 48 < Size.x.bits from by decide, pextLo, pextHi, c13, c17, e8, e9, e10]
    refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    simp only [RegUpd.gpr_write, h1, h2, h5, h6, ↓reduceIte]
    exact k₁.gpr r (by simp [h3, h4])

/-! ## A chunk's low words and matrix -/

/-- A chunk's update of the low words in `x2`, `x3`. -/
theorem plow_ok (s : State) {n : Nat} (hn : n < 64) {g g' : Reg}
    (hg : g = .x9 ∧ g' = .x10 ∨ g = .x10 ∧ g' = .x9) :
    WP isa (.block (plow n g g')) s fun s' =>
      s'.gpr .x2 = (s.gpr .x2 * s.gpr .x8 + s.gpr .x3 * s.gpr .x11) >>> n ∧
      s'.gpr .x3 = (s.gpr .x2 * s.gpr g + s.gpr .x3 * s.gpr g') >>> n ∧
      Keeps [.x2, .x3, .x13, .x16] s s' := by
  apply WP.of_runBlock
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [plow, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
      show n < Size.x.bits from hn]
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    simp only [RegUpd.gpr_write, h1, h2, h3, h4, ↓reduceIte]

/-- The first chunk's matrix into `x4`–`x7`. -/
theorem pfirst_ok (s : State) {g g' : Reg} (hg : g = .x9 ∧ g' = .x10 ∨ g = .x10 ∧ g' = .x9) :
    WP isa (.block (pfirst g g')) s fun s' =>
      s'.gpr .x4 = s.gpr .x8 ∧ s'.gpr .x5 = s.gpr .x11 ∧ s'.gpr .x6 = s.gpr g ∧ s'.gpr .x7 = s.gpr g' ∧
      Keeps [.x4, .x5, .x6, .x7] s s' := by
  apply WP.of_runBlock
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [pfirst, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', BitVec.or_self]
    refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    simp only [RegUpd.gpr_write, h1, h2, h3, h4, ↓reduceIte]

/-- The batch's matrix times the chunk's. -/
theorem pcomp_ok (s : State) {g g' : Reg} (hg : g = .x9 ∧ g' = .x10 ∨ g = .x10 ∧ g' = .x9) :
    WP isa (.block (pcomp g g')) s fun s' =>
      s'.gpr .x4 = s.gpr .x8 * s.gpr .x4 + s.gpr .x11 * s.gpr .x6 ∧
      s'.gpr .x5 = s.gpr .x8 * s.gpr .x5 + s.gpr .x11 * s.gpr .x7 ∧
      s'.gpr .x6 = s.gpr g * s.gpr .x4 + s.gpr g' * s.gpr .x6 ∧
      s'.gpr .x7 = s.gpr g * s.gpr .x5 + s.gpr g' * s.gpr .x7 ∧
      Keeps [.x4, .x5, .x6, .x7, .x13, .x16, .x17] s s' := by
  apply WP.of_runBlock
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [pcomp, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', BitVec.or_self]
    refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    simp only [RegUpd.gpr_write, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

/-! ## A chunk -/

/-- The registers a chunk writes. -/
abbrev chunkRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17]

/-- The state at a chunk's start for the batch's state `T` so far: `~d` in
`x1`, the low words of `f` and `g` in `x2`, `x3` modulo `2^K`, and (but for
the first chunk, whose `T` has the identity) the matrix in `x4`–`x7`. -/
structure ChunkAt (K : Nat) (first : Bool) (T : MSt) (s : State) : Prop where
  d : s.gpr .x1 = ~~~BitVec.ofInt 64 T.d
  f : ((s.gpr .x2).toNat : Int) % 2 ^ K = T.f % 2 ^ K
  g : ((s.gpr .x3).toNat : Int) % 2 ^ K = T.g % 2 ^ K
  id : first = true → T.u = 1 ∧ T.v = 0 ∧ T.q = 0 ∧ T.r = 1
  mat : first = false → s.gpr .x4 = BitVec.ofInt 64 T.u ∧ s.gpr .x5 = BitVec.ofInt 64 T.v ∧
    s.gpr .x6 = BitVec.ofInt 64 T.q ∧ s.gpr .x7 = BitVec.ofInt 64 T.r

/-- A row's start is congruent to the low word modulo `2^n`, `n ≤ 15`. -/
theorem prow_mod {w : BitVec 64} {F : Int} {K n k : Nat} (hn : n ≤ 15) (hK : n ≤ K) (hk : 15 ≤ k)
    (h : (w.toNat : Int) % 2 ^ K = F % 2 ^ K) :
    (((w.toNat % 2 ^ 15 : Nat) : Int) + 2 ^ k) % 2 ^ n = F % 2 ^ n := by
  have d1 : (2 : Int) ^ n ∣ 2 ^ 15 := pow_dvd_pow 2 hn
  have d2 : (2 : Int) ^ n ∣ 2 ^ k := pow_dvd_pow 2 (by omega_arith)
  have d3 : (2 : Int) ^ n ∣ 2 ^ K := pow_dvd_pow 2 hK
  rw [Int.natCast_mod, Nat.cast_pow, Nat.cast_ofNat, Int.add_emod, Int.emod_eq_zero_of_dvd d2, add_zero,
    Int.emod_emod_of_dvd _ d1, Int.emod_emod, ← Int.emod_emod_of_dvd _ d3, h, Int.emod_emod_of_dvd _ d3]

/-- A chunk of `n` steps from the batch's state `T` so far: `T`'s `n` steps. -/
theorem pchunk_ok (s : State) {n K : Nat} {first last : Bool} (hn : 1 ≤ n ∧ n ≤ 15) (hK : n ≤ K ∧ K ≤ 64)
    {T : MSt} (hf : T.f % 2 = 1) (hd : |T.d| + 2 * n < 2 ^ 62) (hI : ChunkAt K first T s) :
    WP isa (.block (pchunk n first last)) s fun s' =>
      s'.gpr .x1 = ~~~BitVec.ofInt 64 (msteps n T).d ∧
      s'.gpr .x4 = BitVec.ofInt 64 (msteps n T).u ∧ s'.gpr .x5 = BitVec.ofInt 64 (msteps n T).v ∧
      s'.gpr .x6 = BitVec.ofInt 64 (msteps n T).q ∧ s'.gpr .x7 = BitVec.ofInt 64 (msteps n T).r ∧
      (last = false → ((s'.gpr .x2).toNat : Int) % 2 ^ (K - n) = (msteps n T).f % 2 ^ (K - n) ∧
        ((s'.gpr .x3).toNat : Int) % 2 ^ (K - n) = (msteps n T).g % 2 ^ (K - n)) ∧
      Keeps chunkRegs s s' := by
  have hmat := Divstep.msteps_mat (d := T.d) (g := T.g) hf n
  have bnd := Divstep.msteps_bnd T.d T.f T.g n
  have lo := Divstep.msteps_lo T.d T.f T.g n
  have hP := prow_mod (w := s.gpr .x2) hn.2 hK.1 (k := 31) (by norm_num) hI.f
  have hQ := prow_mod (w := s.gpr .x3) hn.2 hK.1 (k := 47) (by norm_num) hI.g
  have hrel := Divstep.psteps_rel (d := T.d) (f := T.f) (g := T.g) (n := n) (by omega_arith) hf hd hP hQ n le_rfl
  have hsh := fun k (hk : k < n) => Divstep.psteps_shl (d := T.d) (f := T.f) (g := T.g) (n := n) (by omega_arith)
    hf hd hP hQ hk
  rw [Divstep.msteps_gen n T]
  simp only
  set m := msteps n (MSt.init T.d T.f T.g) with hm
  simp only [pchunk, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pset_ok s) fun s₁ ⟨x8₁, x9₁, x12₁, k₁⟩ => ?_
  rw [pset_int _ _ c31] at x8₁
  rw [pset_int _ _ c47] at x9₁
  have e₁ : (s₁.gpr .x1, s₁.gpr .x8, s₁.gpr .x9) = (~~~BitVec.ofInt 64 T.d,
      BitVec.ofInt 64 ((((s.gpr .x2).toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 31),
      BitVec.ofInt 64 ((((s.gpr .x3).toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 47)) := by
    rw [k₁.gpr _ (by decide), hI.d, x8₁, x9₁]
  rw [WP.block_append_iff]
  refine WP.mono (pstepsCode_ok s₁ hn.2 x12₁ (by rw [e₁]; exact hsh)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, hrel] at e₂
  simp only [Prod.mk.injEq] at e₂
  obtain ⟨d₂, f₂, g₂⟩ := e₂
  have p15 : (2 : Int) ^ n ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) hn.2
  have ha : (s.gpr .x2).toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  have hb : (s.gpr .x3).toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  obtain ⟨eu, ev⟩ := Divstep.pext_rel ha hb (u := m.u) (v := m.v) (by linarith [lo.1]) (by linarith [lo.2.1])
    (by linarith [bnd.1])
  obtain ⟨eq, er⟩ := Divstep.pext_rel ha hb (u := m.q) (v := m.r) (by linarith [lo.2.2.1])
    (by linarith [lo.2.2.2.1]) (by linarith [bnd.2])
  have D : ∀ r ∈ [Reg.x2, .x3, .x4, .x5, .x6, .x7], r ∉ [Reg.x8, .x9, .x12, .x13, .x16] ∧ r ∉ pRegs ∧
      r ∉ [Reg.x8, .x11, .x13, .x17, .x9, .x10] ∧ r ∉ [Reg.x8, .x11, .x13, .x17, .x10, .x9] := by decide
  rcases gReg_cases n with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;>
  · rw [WP.block_append_iff]
    refine WP.mono (pext_ok s₂ (by rw [hA, hB]; decide)) fun s₃ ⟨u₃, v₃, q₃, r₃, k₃⟩ => ?_
    rw [f₂, eu] at u₃
    rw [f₂, ev] at v₃
    rw [g₂, eq] at q₃
    rw [g₂, er] at r₃
    have d₃ : s₃.gpr .x1 = ~~~BitVec.ofInt 64 m.d := by rw [k₃.gpr _ (by rw [hA, hB]; decide), d₂]
    have R₃ : ∀ r ∈ [Reg.x2, .x3, .x4, .x5, .x6, .x7], s₃.gpr r = s.gpr r := fun r hr => by
      obtain ⟨a, b, c, c'⟩ := D r hr
      rw [k₃.gpr r (by rw [hA, hB]; first | exact c | exact c'), k₂.gpr r b, k₁.gpr r a]
    rw [WP.block_append_iff]
    have hlow : WP isa (.block (if last = true then [] else plow n (gReg n) (gReg (n + 1)))) s₃ fun s₄ =>
        (∀ r ∈ [Reg.x1, .x4, .x5, .x6, .x7, .x8, .x11, gReg n, gReg (n + 1)], s₄.gpr r = s₃.gpr r) ∧
        (last = false → ((s₄.gpr .x2).toNat : Int) % 2 ^ (K - n) = m.f % 2 ^ (K - n) ∧
          ((s₄.gpr .x3).toNat : Int) % 2 ^ (K - n) = m.g % 2 ^ (K - n)) ∧
        Keeps [.x2, .x3, .x13, .x16] s₃ s₄ := by
      cases last
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have dl : ∀ r ∈ [Reg.x1, .x4, .x5, .x6, .x7, .x8, .x11, gReg n, gReg (n + 1)],
            r ∉ [Reg.x2, .x3, .x13, .x16] := by rw [hA, hB]; decide
        refine WP.mono (plow_ok s₃ (n := n) (by omega_arith) (by rw [hA, hB]; decide)) fun s₄ ⟨w2, w3, k₄⟩ =>
          ⟨fun r hr => k₄.gpr r (dl r hr), fun _ => ⟨?_, ?_⟩, k₄⟩
        · rw [w2, R₃ .x2 (by decide), R₃ .x3 (by decide), u₃, v₃]
          exact Divstep.low_upd hK.2 hK.1 hI.f hI.g hmat.1
        · rw [w3, R₃ .x2 (by decide), R₃ .x3 (by decide), q₃, r₃]
          exact Divstep.low_upd hK.2 hK.1 hI.f hI.g hmat.2
      · simp only [↓reduceIte]
        exact WP.block_nil_iff.mpr ⟨fun _ _ => rfl, fun h => absurd h (by decide), fun _ _ => rfl, rfl, rfl, rfl,
          rfl⟩
    refine WP.mono hlow fun s₄ ⟨R₄, w₄, k₄⟩ => ?_
    have k34 : Keeps chunkRegs s s₄ := (((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by rw [hA, hB]; decide))).trans (k₄.mono (by decide))
    have x1₄ : s₄.gpr .x1 = ~~~BitVec.ofInt 64 m.d := by rw [R₄ _ (by simp), d₃]
    cases first
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨m4, m5, m6, m7⟩ := hI.mat rfl
      refine WP.mono (pcomp_ok s₄ (by rw [hA, hB]; decide)) fun s₅ ⟨x4₅, x5₅, x6₅, x7₅, k₅⟩ =>
        ⟨by rw [k₅.gpr _ (by decide), x1₄], ?_, ?_, ?_, ?_, fun h => ?_, k34.trans (k₅.mono (by decide))⟩
      · rw [x4₅, R₄ .x8 (by simp), R₄ .x11 (by simp), R₄ .x4 (by simp), R₄ .x6 (by simp), u₃, v₃,
          R₃ .x4 (by decide), R₃ .x6 (by decide), m4, m6, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
          ← BitVec.ofInt_add]
      · rw [x5₅, R₄ .x8 (by simp), R₄ .x11 (by simp), R₄ .x5 (by simp), R₄ .x7 (by simp), u₃, v₃,
          R₃ .x5 (by decide), R₃ .x7 (by decide), m5, m7, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
          ← BitVec.ofInt_add]
      · rw [x6₅, R₄ (gReg n) (by simp), R₄ (gReg (n + 1)) (by simp), R₄ .x4 (by simp), R₄ .x6 (by simp), q₃, r₃,
          R₃ .x4 (by decide), R₃ .x6 (by decide), m4, m6, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
          ← BitVec.ofInt_add]
      · rw [x7₅, R₄ (gReg n) (by simp), R₄ (gReg (n + 1)) (by simp), R₄ .x5 (by simp), R₄ .x7 (by simp), q₃, r₃,
          R₃ .x5 (by decide), R₃ .x7 (by decide), m5, m7, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
          ← BitVec.ofInt_add]
      · obtain ⟨wf, wg⟩ := w₄ h
        exact ⟨by rw [k₅.gpr _ (by decide)]; exact wf, by rw [k₅.gpr _ (by decide)]; exact wg⟩
    · simp only [↓reduceIte]
      obtain ⟨i1, i2, i3, i4⟩ := hI.id rfl
      refine WP.mono (pfirst_ok s₄ (by rw [hA, hB]; decide)) fun s₅ ⟨x4₅, x5₅, x6₅, x7₅, k₅⟩ =>
        ⟨by rw [k₅.gpr _ (by decide), x1₄], ?_, ?_, ?_, ?_, fun h => ?_, k34.trans (k₅.mono (by decide))⟩
      · rw [x4₅, R₄ .x8 (by simp), u₃, i1, i3, mul_one, mul_zero, add_zero]
      · rw [x5₅, R₄ .x11 (by simp), v₃, i2, i4, mul_one, mul_zero, zero_add]
      · rw [x6₅, R₄ (gReg n) (by simp), q₃, i1, i3, mul_one, mul_zero, add_zero]
      · rw [x7₅, R₄ (gReg (n + 1)) (by simp), r₃, i2, i4, mul_one, mul_zero, zero_add]
      · obtain ⟨wf, wg⟩ := w₄ h
        exact ⟨by rw [k₅.gpr _ (by decide)]; exact wf, by rw [k₅.gpr _ (by decide)]; exact wg⟩

/-! ## A batch's steps -/

/-- `x1 = ~x1`. -/
theorem notD_ok (s : State) :
    WP isa (.block notD) s fun s' => s'.gpr .x1 = ~~~s.gpr .x1 ∧ Keeps [.x1, .x13] s s' := by
  apply WP.of_runBlock
  simp only [notD, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
    show 16 * 0 < Size.x.bits from by decide, show (1 : Nat) < 4096 from by decide]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [BitVec.not_eq_neg_add, ← BitVec.zero_sub]
    exact congrArg (· - s.gpr .x1 - _) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ↓reduceIte]

theorem msteps_d15 {T : MSt} {k : Nat} (h : |T.d| + 2 * k ≤ 2 ^ 31) :
    |(msteps 15 T).d| + 2 * k ≤ 2 ^ 31 + 30 := by
  have := Divstep.msteps_d T 15; push_cast at this; omega_arith

/-- A batch's `59` divsteps in chunks, from `d` in `x1` and the low words of
`f` and `g` in `x2`, `x3`: `d` and the matrix in `x1`, `x4`–`x7`. -/
theorem pwords_ok (s : State) {d f g : Int} (hd : |d| ≤ 2 ^ 30) (hf : f % 2 = 1)
    (h1 : s.gpr .x1 = BitVec.ofInt 64 d) (h2 : ((s.gpr .x2).toNat : Int) % 2 ^ 64 = f % 2 ^ 64)
    (h3 : ((s.gpr .x3).toNat : Int) % 2 ^ 64 = g % 2 ^ 64) :
    WP isa (.block pwords) s fun t =>
      t.gpr .x1 = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).d ∧
      t.gpr .x4 = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).u ∧
      t.gpr .x5 = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).v ∧
      t.gpr .x6 = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).q ∧
      t.gpr .x7 = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).r ∧ Keeps chunkRegs s t := by
  set T0 := MSt.init d f g with hT0
  have f0 : T0.f % 2 = 1 := hf
  have odd : ∀ k, (msteps k T0).f % 2 = 1 := Divstep.msteps_f_odd f0
  have dd : ∀ k, |(msteps k T0).d| ≤ 2 ^ 30 + 2 * k := fun k => by
    have := Divstep.msteps_d T0 k
    rw [show T0.d = d from rfl] at this
    omega_arith
  simp only [pwords, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (notD_ok s) fun s₁ ⟨b₁, k₁⟩ => ?_
  have c₁ : ChunkAt 64 true T0 s₁ :=
    ⟨by rw [b₁, h1]; rfl, by rw [k₁.gpr _ (by decide)]; exact h2, by rw [k₁.gpr _ (by decide)]; exact h3,
      fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => absurd h (by decide)⟩
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok s₁ (n := 15) (K := 64) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ f0 (by rw [show T0.d = d from rfl]; push_cast; omega_arith) c₁)
    fun s₂ ⟨d₂, u₂, v₂, q₂, r₂, w₂, k₂⟩ => ?_
  obtain ⟨f₂, g₂⟩ := w₂ rfl
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok s₂ (n := 15) (K := 49) (first := false) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ (odd 15) (by have := dd 15; norm_num at this ⊢; omega_arith)
    ⟨d₂, f₂, g₂, fun h => absurd h (by decide), fun _ => ⟨u₂, v₂, q₂, r₂⟩⟩)
    fun s₃ ⟨d₃, u₃, v₃, q₃, r₃, w₃, k₃⟩ => ?_
  obtain ⟨f₃, g₃⟩ := w₃ rfl
  rw [← Divstep.msteps_add] at d₃ u₃ v₃ q₃ r₃ f₃ g₃
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok s₃ (n := 15) (K := 34) (first := false) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ (odd 30) (by have := dd 30; norm_num at this ⊢; omega_arith)
    ⟨d₃, f₃, g₃, fun h => absurd h (by decide), fun _ => ⟨u₃, v₃, q₃, r₃⟩⟩)
    fun s₄ ⟨d₄, u₄, v₄, q₄, r₄, w₄, k₄⟩ => ?_
  obtain ⟨f₄, g₄⟩ := w₄ rfl
  rw [← Divstep.msteps_add] at d₄ u₄ v₄ q₄ r₄ f₄ g₄
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok s₄ (n := 14) (K := 19) (first := false) (last := true) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ (odd 45) (by have := dd 45; norm_num at this ⊢; omega_arith)
    ⟨d₄, f₄, g₄, fun h => absurd h (by decide), fun _ => ⟨u₄, v₄, q₄, r₄⟩⟩)
    fun s₅ ⟨d₅, u₅, v₅, q₅, r₅, _, k₅⟩ => ?_
  rw [← Divstep.msteps_add] at d₅ u₅ v₅ q₅ r₅
  refine WP.mono (notD_ok s₅) fun t ⟨b, k⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b, d₅, BitVec.not_not]
  · rw [k.gpr _ (by decide), u₅]
  · rw [k.gpr _ (by decide), v₅]
  · rw [k.gpr _ (by decide), q₅]
  · rw [k.gpr _ (by decide), r₅]
  · exact ((((k₁.mono (by decide)).trans k₂).trans k₃).trans k₄).trans k₅ |>.trans (k.mono (by decide))

end VG.Proof.Weierstrass.AArch64
