module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Divstep.PackedDef
public import VerifiedGarbage.Proof.Divstep.Steps
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Iter
import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.Divstep.SignedWords
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.WordBasic
import VerifiedGarbage.Proof.Ed25519.Group.Extended
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvPacked
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop

/-!
# Ed25519 and X25519 on AArch64: the inversion by divsteps is correct

Each batch keeps the invariant `BatchInv`: `f` and `g` are those of `59 k` divsteps
from `(1, p, x)`, and `2^590 x a ≡ 2^(59 k) f`, `2^590 x b ≡ 2^(59 k) g` modulo `p`
(`batch_ok`). After 590 divsteps `g = 0` and `f = ±1`, so `x a ≡ ±1`, and
`x^(p - 2)` is the inverse, as `p` is prime.

The parts: a batch's packed divsteps, the arithmetic of its update, the update,
the ends, and the theorem.
-/

@[expose] public section

/-! # A batch's packed divsteps

A step's block is `mstep`'s on the rows (`step_ok`), with `i = (d - 1) / 2` in
`x20`, a chunk's block its steps from the batch's state so far (`Chunk`), and
the batch's four chunks leave `i` and the matrix of 59 steps (`words_ok`).
-/

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Divstep (MSt mstep msteps pextLo pextHi ite_t ite_f)
open VG.Proof.Weierstrass.AArch64 (one64 add_not0_one' and_mask_iff pset_int prow_mod c31 c47)

/-! ## A step -/

/-- The registers a chunk's steps write. -/
abbrev stepRegs : List Reg := [.x20, .x8, .x9, .x10, .x11, .x12, .x13, .x16]

/-- A step's block, for each kind of step. -/
theorem stepCode_run (s : State) {g t : Reg} (hg : g = .x9 ∧ t = .x10 ∨ g = .x10 ∧ t = .x9)
    {odd neg : Bool} (hz : decide (s.gpr g &&& s.gpr .x12 = 0) = !odd) (hn : (s.gpr .x20).msb = neg) :
    WP isa (.block (stepCode g t)) s fun s' =>
      s'.gpr .x20 = (if odd && !neg then -s.gpr .x20 else s.gpr .x20 + 1) ∧
      s'.gpr .x8 = (if odd && !neg then s.gpr g + s.gpr g else s.gpr .x8 + s.gpr .x8) ∧
      s'.gpr t = (if odd && !neg then s.gpr g - s.gpr .x8 else if odd then s.gpr g + s.gpr .x8 else s.gpr g) ∧
      s'.gpr .x12 = s.gpr .x12 + s.gpr .x12 ∧ Keeps [.x20, .x8, .x11, .x12, .x13, .x16, t] s s' := by
  apply WP.of_runBlock
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases odd <;>
  · simp only [stepCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', CondCode.holds,
      State.flagsAdd, hz, Bool.toNat_true, one64, add_not0_one', hn, show (1 : Nat) < 4096 from by decide,
      show (0 : Nat) < 32 ∧ (8 : Nat) < 16 from by decide, and_self,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
      show Nat.testBit 8 3 = true by decide, RegUpd.nf_write, RegUpd.zf_write, Bool.false_eq_true]
    refine ⟨by first | trivial | cases neg <;> rfl, by first | trivial | cases neg <;> rfl,
      by first | trivial | cases neg <;> rfl, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    simp only [RegUpd.gpr_write, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

/-- Bit `j` of a word congruent to `2^j b` modulo `2^(j + 1)`. -/
theorem row_bit {X b : Int} {j : Nat} (hj : j ≤ 62) (hb : b = 0 ∨ b = 1) (h : X % 2 ^ (j + 1) = 2 ^ j * b) :
    (BitVec.ofInt 64 X).getLsbD j = decide (b = 1) := by
  obtain hs := Divstep.shl_bit hj hb h
  obtain hb63 := Weierstrass.AArch64.shl_getLsbD (BitVec.ofInt 64 X) (j := j) (by omega_using [hj])
  rw [← hb63, ← BitVec.testBit_toNat, hs]
  rcases hb with rfl | rfl
  · decide
  · rw [Int.toNat_one, Nat.mul_one, Nat.testBit_two_pow_self]; rfl

/-- `i = (d - 1) / 2` as a word. -/
abbrev half (d : Int) : BitVec 64 := BitVec.ofInt 64 ((d - 1) / 2)

theorem half_msb {d : Int} (hd : |d| < 2 ^ 62) (ho : d % 2 = 1) : (half d).msb = !decide (0 ≤ d) := by
  rw [abs_lt] at hd
  rw [half, BitVec.msb_eq_toInt, BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega_using [hd]) (by omega_using [hd])]
  by_cases h : 0 ≤ d
  · rw [decide_eq_true h, decide_eq_false (by omega_using [h, ho])]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega_using [h, ho])]; rfl

/-- The rows and `i` of `t`, from the rows' starts `P` and `Q`. -/
structure Rows (P Q : Int) (g : Reg) (t : MSt) (s : State) : Prop where
  i : s.gpr .x20 = half t.d
  f : s.gpr .x8 = BitVec.ofInt 64 (t.u * P + t.v * Q)
  g : s.gpr g = BitVec.ofInt 64 (t.q * P + t.r * Q)

theorem mstep_d_odd {t : MSt} (h : t.d % 2 = 1) : (mstep t).d % 2 = 1 := by
  unfold mstep; split <;> simp only <;> omega_using [h]

theorem msteps_d_odd {t : MSt} (h : t.d % 2 = 1) : ∀ n, (msteps n t).d % 2 = 1
  | 0 => h
  | n + 1 => by rw [Divstep.msteps_succ]; exact mstep_d_odd (msteps_d_odd h n)

/-- Step `j`: `mstep`. -/
theorem step_ok (s : State) {j : Nat} (hj : j ≤ 62) {g t : Reg}
    (hg : g = .x9 ∧ t = .x10 ∨ g = .x10 ∧ t = .x9) (hm : s.gpr .x12 = BitVec.ofNat 64 (2 ^ j))
    {P Q : Int} {T : MSt} (hd : |T.d| < 2 ^ 62) (ho : T.d % 2 = 1) (hR : Rows P Q g T s)
    (hG : (T.q * P + T.r * Q) % 2 ^ (j + 1) = 2 ^ j * (T.g % 2)) :
    WP isa (.block (stepCode g t)) s fun s' =>
      Rows P Q t (mstep T) s' ∧ s'.gpr .x12 = BitVec.ofNat 64 (2 ^ (j + 1)) ∧ Keeps stepRegs s s' := by
  obtain hb := Int.emod_two_eq_zero_or_one T.g
  obtain hbit := row_bit hj hb hG
  obtain hmsb := half_msb hd ho
  obtain m2 : s.gpr .x12 + s.gpr .x12 = BitVec.ofNat 64 (2 ^ (j + 1)) := by
    rw [hm, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]
  have sub : ∀ r ∈ [Reg.x20, .x8, .x11, .x12, .x13, .x16, t], r ∈ stepRegs := by
    rcases hg with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  refine WP.mono (stepCode_run s hg (odd := decide (T.g % 2 = 1)) (neg := !decide (0 ≤ T.d)) ?_ (by rw [hR.i, hmsb]))
    fun s' ⟨e20, e8, et, e12, k⟩ => ⟨?_, by rw [e12, m2], k.mono sub⟩
  · rw [hm, hR.g, ← hbit]
    cases h : (BitVec.ofInt 64 (T.q * P + T.r * Q)).getLsbD j
    · exact decide_eq_true ((and_mask_iff _ (by omega_using [hj])).mpr h)
    · refine decide_eq_false fun h' => ?_
      rw [(and_mask_iff _ (by omega_using [hj])).mp h'] at h
      exact absurd h (by decide)
  · rw [hR.i] at e20
    rw [hR.f, hR.g] at e8
    rw [hR.f, hR.g] at et
    have h1 : (1 : BitVec 64) = BitVec.ofInt 64 1 := by decide
    rw [Bool.not_not] at e20 e8 et
    by_cases hc : 0 ≤ T.d ∧ T.g % 2 = 1
    · have hsw : (decide (T.g % 2 = 1) && decide (0 ≤ T.d)) = true := by simp only [hc, decide_true, Bool.and_self]
      rw [ite_t hsw] at e20 e8 et
      have hT : mstep T = ⟨2 - T.d, T.g, (T.g - T.f) / 2, 2 * T.q, 2 * T.r, T.q - T.u, T.r - T.v⟩ := by
        unfold mstep; exact ite_t hc
      rw [hT]
      refine ⟨?_, ?_, ?_⟩
      · rw [e20, half, half, ← BitVec.ofInt_neg]; congr 1; dsimp only; omega_using [ho]
      · rw [e8, Divstep.oadd]; congr 1; ring
      · rw [et, Divstep.osub]; congr 1; ring
    · have hsw : ¬ (decide (T.g % 2 = 1) && decide (0 ≤ T.d)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; exact fun h => hc ⟨h.2, h.1⟩
      rw [ite_f hsw] at e20 e8 et
      have hT : mstep T = ⟨2 + T.d, T.f, (T.g + T.g % 2 * T.f) / 2, 2 * T.u, 2 * T.v, T.q + T.g % 2 * T.u,
          T.r + T.g % 2 * T.v⟩ := by unfold mstep; exact ite_f hc
      rw [hT]
      refine ⟨?_, ?_, ?_⟩
      · rw [e20, half, half, h1, Divstep.oadd]; congr 1; dsimp only; omega_using []
      · rw [e8, Divstep.oadd]; congr 1; ring
      · rcases hb with h | h
        · rw [ite_f (by rw [h]; decide)] at et
          rw [et, h]; congr 1; ring
        · rw [ite_t (by rw [h]; decide), Divstep.oadd] at et
          rw [et, h]; congr 1; ring

theorem gReg_cases (j : Nat) : gReg j = .x9 ∧ gReg (j + 1) = .x10 ∨ gReg j = .x10 ∧ gReg (j + 1) = .x9 := by
  unfold gReg
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · left; exact ⟨ite_t h, ite_f (by omega_using [h])⟩
  · right; exact ⟨ite_f (by omega_using [h]), ite_t (by omega_using [h])⟩

/-- A chunk's first `k ≤ n` steps, from `P ≡ f` and `Q ≡ g` modulo `2^n`. -/
theorem steps_ok (s : State) {d f g P Q : Int} {n : Nat} (hn : n ≤ 62) (hm : s.gpr .x12 = 1) (hf : f % 2 = 1)
    (hd : |d| + 2 * n < 2 ^ 62) (ho : d % 2 = 1) (hP : P % 2 ^ n = f % 2 ^ n) (hQ : Q % 2 ^ n = g % 2 ^ n)
    (hR : Rows P Q .x9 (MSt.init d f g) s) :
    ∀ k ≤ n, WP isa (.block (stepsCode k)) s fun s' =>
      Rows P Q (gReg k) (msteps k (MSt.init d f g)) s' ∧ s'.gpr .x12 = BitVec.ofNat 64 (2 ^ k) ∧
      Keeps stepRegs s s'
  | 0, _ => WP.block_nil_iff.mpr ⟨hR, by rw [hm]; rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk => by
    rw [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (steps_ok s hn hm hf hd ho hP hQ hR k (by omega_using [hk])) fun s₁ ⟨R₁, m₁, k₁⟩ => ?_
    have hd' := Divstep.msteps_d (MSt.init d f g) k
    rw [show (MSt.init d f g).d = d from rfl] at hd'
    refine WP.mono (step_ok s₁ (by omega_using [hn, hk]) (gReg_cases k) m₁ ?_ (msteps_d_odd (by exact ho) k) R₁ ?_)
      fun s₂ ⟨R₂, m₂, k₂⟩ => ⟨by rw [Divstep.msteps_succ]; exact R₂, m₂, k₁.trans k₂⟩
    · have : (2 * k : Int) ≤ 2 * n := by exact_mod_cast (by omega_using [hk] : 2 * k ≤ 2 * n)
      linarith
    · obtain ⟨-, mg⟩ := Divstep.msteps_mat (d := d) (g := g) hf k
      have hdv : (2 : Int) ^ (k + 1) ∣ 2 ^ n := pow_dvd_pow 2 hk
      rw [← Divstep.pow_mul_emod_succ, mg, ← Int.emod_emod_of_dvd _ hdv, ← Int.emod_emod_of_dvd (_ * f + _) hdv]
      congr 1
      rw [Int.add_emod, Int.mul_emod _ P, hP, ← Int.mul_emod, Int.mul_emod _ Q, hQ, ← Int.mul_emod, ← Int.add_emod]

/-! ## A chunk's other blocks -/

/-- The chunks' constants. -/
structure Consts (s : State) : Prop where
  c14 : s.gpr .x14 = Divstep.pextC
  c15 : s.gpr .x15 = 0x7fff
  c17 : s.gpr .x17 = 16384

theorem consts_ok (s : State) : WP isa (.block consts) s fun s' => Consts s' ∧ Keeps [.x14, .x15, .x17] s s' := by
  apply WP.of_runBlock
  simp only [consts, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, ↓reduceIte, Option.some.injEq, exists_eq_left',
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide]
  refine ⟨⟨?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ↓reduceIte]; decide
  · simp only [RegUpd.gpr_write, reduceCtorEq, ↓reduceIte]; decide
  · simp only [RegUpd.gpr_write, ↓reduceIte]; decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ↓reduceIte]

/-- A `movk` of a word below `2^15` at bits 16 or 32 up is an addition. -/
theorem movk_low (w : BitVec 64) :
    ((w &&& 0x7fff#64) &&& ~~~(0xffff#64 <<< 16)) ||| ((0x8000#16).setWidth 64 <<< 16) = (w &&& 0x7fff#64) + 2 ^ 31 ∧
    ((w &&& 0x7fff#64) &&& ~~~(0xffff#64 <<< 32)) ||| ((0x8000#16).setWidth 64 <<< 32) = (w &&& 0x7fff#64) + 2 ^ 47 := by
  have c (K L : BitVec 64) (hK : 0x7fff#64 &&& K = L) : (w &&& 0x7fff#64) &&& K = w &&& L := by
    rw [BitVec.and_assoc, hK]
  have z (K : BitVec 64) (hK : 0x7fff#64 &&& K = 0#64) : (w &&& 0x7fff#64) &&& K = 0#64 := by
    rw [c _ _ hK, BitVec.and_zero]
  refine ⟨?_, ?_⟩
  · rw [c _ 0x7fff#64 (by decide), show ((0x8000#16).setWidth 64 <<< 16) = (2 ^ 31 : BitVec 64) by decide,
      BitVec.add_eq_or_of_and_eq_zero _ _ (z _ (by decide))]
  · rw [c _ 0x7fff#64 (by decide), show ((0x8000#16).setWidth 64 <<< 32) = (2 ^ 47 : BitVec 64) by decide,
      BitVec.add_eq_or_of_and_eq_zero _ _ (z _ (by decide))]

theorem rowsStart_ok (s : State) (hc : Consts s) :
    WP isa (.block rowsStart) s fun s' =>
      s'.gpr .x8 = (s.gpr .x2 &&& 0x7fff) + 2 ^ 31 ∧ s'.gpr .x9 = (s.gpr .x3 &&& 0x7fff) + 2 ^ 47 ∧
      s'.gpr .x12 = 1 ∧ Keeps [.x8, .x9, .x12] s s' := by
  apply WP.of_runBlock
  simp only [rowsStart, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', hc.c15,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide]
  refine ⟨(movk_low _).1, (movk_low _).2, by decide, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ↓reduceIte]

/-- The registers of a row's entries. -/
abbrev EntryRegs (w l h : Reg) : Prop :=
  w = .x8 ∧ l = .x4 ∧ h = .x5 ∨ w = .x10 ∧ l = .x6 ∧ h = .x7 ∨ w = .x8 ∧ l = .x8 ∧ h = .x11 ∨
    w = .x10 ∧ l = .x10 ∧ h = .x9 ∨ w = .x9 ∧ l = .x9 ∧ h = .x10

theorem entries_ok (s : State) (hc : Consts s) {w l h : Reg} (hr : EntryRegs w l h) :
    WP isa (.block (entries w l h)) s fun s' =>
      s'.gpr l = pextLo (s.gpr w) ∧ s'.gpr h = pextHi (s.gpr w) ∧ Keeps [w, l, h] s s' := by
  apply WP.of_runBlock
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · simp only [entries, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
      show 47 < Size.x.bits from by decide, show 17 < Size.x.bits from by decide,
      show 48 < Size.x.bits from by decide, pextLo, pextHi, hc.c14, hc.c17]
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ↓reduceIte]

/-- The registers of a chunk's matrix. -/
abbrev MatRegs (u v q r : Reg) : Prop :=
  u = .x4 ∧ v = .x5 ∧ q = .x6 ∧ r = .x7 ∨ u = .x8 ∧ v = .x11 ∧ q = .x10 ∧ r = .x9 ∨
    u = .x8 ∧ v = .x11 ∧ q = .x9 ∧ r = .x10

theorem lows_ok (s : State) {n : Nat} (hn : n < 64) {u v q r : Reg} (hr : MatRegs u v q r) :
    WP isa (.block (lows n u v q r)) s fun s' =>
      s'.gpr .x2 = (s.gpr .x2 * s.gpr u + s.gpr .x3 * s.gpr v) >>> n ∧
      s'.gpr .x3 = (s.gpr .x2 * s.gpr q + s.gpr .x3 * s.gpr r) >>> n ∧
      Keeps [.x2, .x3, .x13, .x16] s s' := by
  apply WP.of_runBlock
  rcases hr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  · simp only [lows, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
      show n < Size.x.bits from hn]
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ↓reduceIte]

theorem compose_ok (s : State) {u v q r : Reg}
    (hr : u = .x8 ∧ v = .x11 ∧ q = .x10 ∧ r = .x9 ∨ u = .x8 ∧ v = .x11 ∧ q = .x9 ∧ r = .x10) :
    WP isa (.block (compose u v q r)) s fun s' =>
      s'.gpr .x4 = s.gpr u * s.gpr .x4 + s.gpr v * s.gpr .x6 ∧
      s'.gpr .x5 = s.gpr u * s.gpr .x5 + s.gpr v * s.gpr .x7 ∧
      s'.gpr .x6 = s.gpr q * s.gpr .x4 + s.gpr r * s.gpr .x6 ∧
      s'.gpr .x7 = s.gpr q * s.gpr .x5 + s.gpr r * s.gpr .x7 ∧
      Keeps [.x4, .x5, .x6, .x7, .x13, .x16] s s' := by
  apply WP.of_runBlock
  rcases hr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  · simp only [compose, column, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
      read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ↓reduceIte]

/-! ## The chunks -/

/-- The registers a batch's divsteps write. -/
abbrev wordRegs : List Reg :=
  [.x20, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The registers a chunk writes. -/
abbrev chunkRegs : List Reg :=
  [.x20, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16]

/-- The state between chunks, for the batch's state `T` so far: `i`, the low
words of `f` and `g` modulo `2^K`. -/
structure Low (K : Nat) (T : MSt) (s : State) : Prop where
  i : s.gpr .x20 = half T.d
  f : ((s.gpr .x2).toNat : Int) % 2 ^ K = T.f % 2 ^ K
  g : ((s.gpr .x3).toNat : Int) % 2 ^ K = T.g % 2 ^ K

/-- The matrix so far. -/
structure Mat (T : MSt) (s : State) : Prop where
  u : s.gpr .x4 = BitVec.ofInt 64 T.u
  v : s.gpr .x5 = BitVec.ofInt 64 T.v
  q : s.gpr .x6 = BitVec.ofInt 64 T.q
  r : s.gpr .x7 = BitVec.ofInt 64 T.r

/-- A chunk's rows and steps: the rows give the matrix of `n` steps. -/
theorem rows_ok (s : State) {n K : Nat} (hn : n ≤ 15) (hK : n ≤ K) (hc : Consts s)
    {T : MSt} (hf : T.f % 2 = 1) (ho : T.d % 2 = 1) (hd : |T.d| + 2 * n < 2 ^ 62) (hI : Low K T s) :
    WP isa (.block (rowsStart ++ stepsCode n)) s fun s' =>
      let m := msteps n (MSt.init T.d T.f T.g)
      s'.gpr .x20 = half m.d ∧
      pextLo (s'.gpr .x8) = BitVec.ofInt 64 m.u ∧ pextHi (s'.gpr .x8) = BitVec.ofInt 64 m.v ∧
      pextLo (s'.gpr (gReg n)) = BitVec.ofInt 64 m.q ∧ pextHi (s'.gpr (gReg n)) = BitVec.ofInt 64 m.r ∧
      Keeps stepRegs s s' := by
  obtain bnd := Divstep.msteps_bnd T.d T.f T.g n
  obtain lo := Divstep.msteps_lo T.d T.f T.g n
  obtain hP := prow_mod (w := s.gpr .x2) hn hK (k := 31) (by norm_num) hI.f
  obtain hQ := prow_mod (w := s.gpr .x3) hn hK (k := 47) (by norm_num) hI.g
  rw [WP.block_append_iff]
  refine WP.mono (rowsStart_ok s hc) fun s₁ ⟨x8₁, x9₁, x12₁, k₁⟩ => ?_
  rw [pset_int _ _ c31] at x8₁
  rw [pset_int _ _ c47] at x9₁
  have R : Rows (((s.gpr .x2).toNat % 2 ^ 15 : Nat) + 2 ^ 31) (((s.gpr .x3).toNat % 2 ^ 15 : Nat) + 2 ^ 47) .x9
      (MSt.init T.d T.f T.g) s₁ := by
    refine ⟨by rw [k₁.gpr _ (by decide)]; exact hI.i, ?_, ?_⟩
    · rw [x8₁]; simp only [MSt.init, one_mul, zero_mul, add_zero]
    · rw [x9₁]; simp only [MSt.init, one_mul, zero_mul, zero_add]
  refine WP.mono (steps_ok s₁ (n := n) (by omega_using [hn]) x12₁ hf hd ho hP hQ R n le_rfl)
    fun s₂ ⟨R₂, _, k₂⟩ => ?_
  obtain p15 : (2 : Int) ^ n ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) hn
  obtain ha : (s.gpr .x2).toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  obtain hb : (s.gpr .x3).toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  intro m
  obtain ⟨eu, ev⟩ := Divstep.pext_rel ha hb (u := m.u) (v := m.v) (by linarith [lo.1]) (by linarith [lo.2.1])
    (by linarith [bnd.1])
  obtain ⟨eq, er⟩ := Divstep.pext_rel ha hb (u := m.q) (v := m.r) (by linarith [lo.2.2.1])
    (by linarith [lo.2.2.2.1]) (by linarith [bnd.2])
  exact ⟨R₂.i, by rw [R₂.f]; exact eu, by rw [R₂.f]; exact ev, by rw [R₂.g]; exact eq, by rw [R₂.g]; exact er,
    (k₁.mono (by decide)).trans k₂⟩

/-- A chunk's matrix in `u`, `v`, `q`, `r`. -/
structure ChunkMat (m : MSt) (u v q r : Reg) (s : State) : Prop where
  u : s.gpr u = BitVec.ofInt 64 m.u
  v : s.gpr v = BitVec.ofInt 64 m.v
  q : s.gpr q = BitVec.ofInt 64 m.q
  r : s.gpr r = BitVec.ofInt 64 m.r

/-- A chunk's rows, steps and entries. -/
theorem matrix_ok (s : State) {n K : Nat} (hn : n ≤ 15) (hK : n ≤ K) (hc : Consts s)
    {T : MSt} (hf : T.f % 2 = 1) (ho : T.d % 2 = 1) (hd : |T.d| + 2 * n < 2 ^ 62) (hI : Low K T s)
    {u v q r : Reg}
    (hr : gReg n = .x10 ∧ u = .x4 ∧ v = .x5 ∧ q = .x6 ∧ r = .x7 ∨
      gReg n = .x10 ∧ u = .x8 ∧ v = .x11 ∧ q = .x10 ∧ r = .x9 ∨
      gReg n = .x9 ∧ u = .x8 ∧ v = .x11 ∧ q = .x9 ∧ r = .x10) :
    WP isa (.block (rowsStart ++ stepsCode n ++ entries .x8 u v ++ entries (gReg n) q r)) s fun s' =>
      let m := msteps n (MSt.init T.d T.f T.g)
      s'.gpr .x20 = half m.d ∧ ChunkMat m u v q r s' ∧ Keeps (stepRegs ++ [u, v, q, r]) s s' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (rows_ok s hn hK hc hf ho hd hI) fun s₁ ⟨d₁, u₁, v₁, q₁, r₁, k₁⟩ => ?_
  have c₁ : Consts s₁ := ⟨by rw [k₁.gpr _ (by decide)]; exact hc.c14, by rw [k₁.gpr _ (by decide)]; exact hc.c15,
    by rw [k₁.gpr _ (by decide)]; exact hc.c17⟩
  have D : EntryRegs .x8 u v ∧ EntryRegs (gReg n) q r ∧ (.x14 ∉ [Reg.x8, u, v] ∧ .x15 ∉ [Reg.x8, u, v] ∧
      .x17 ∉ [Reg.x8, u, v] ∧ gReg n ∉ [Reg.x8, u, v] ∧ .x20 ∉ [Reg.x8, u, v]) ∧
      (.x20 ∉ [gReg n, q, r] ∧ u ∉ [gReg n, q, r] ∧ v ∉ [gReg n, q, r]) ∧
      (∀ a ∈ [Reg.x8, u, v], a ∈ stepRegs ++ [u, v, q, r]) ∧ (∀ a ∈ [gReg n, q, r], a ∈ stepRegs ++ [u, v, q, r]) := by
    rcases hr with ⟨h, rfl, rfl, rfl, rfl⟩ | ⟨h, rfl, rfl, rfl, rfl⟩ | ⟨h, rfl, rfl, rfl, rfl⟩ <;> rw [h] <;> decide
  obtain ⟨D1, D2, ⟨n14, n15, n17, ng, n20⟩, ⟨n20', nu, nv⟩, i1, i2⟩ := D
  rw [WP.block_append_iff]
  refine WP.mono (entries_ok s₁ c₁ D1) fun s₂ ⟨l₂, h₂, k₂⟩ => ?_
  have c₂ : Consts s₂ := ⟨by rw [k₂.gpr _ n14]; exact c₁.c14, by rw [k₂.gpr _ n15]; exact c₁.c15,
    by rw [k₂.gpr _ n17]; exact c₁.c17⟩
  refine WP.mono (entries_ok s₂ c₂ D2) fun s₃ ⟨l₃, h₃, k₃⟩ => ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [k₃.gpr _ n20', k₂.gpr _ n20, d₁]
  · rw [k₃.gpr _ nu, l₂, u₁]
  · rw [k₃.gpr _ nv, h₂, v₁]
  · rw [l₃, k₂.gpr _ ng, q₁]
  · rw [h₃, k₂.gpr _ ng, r₁]
  · exact ((k₁.mono fun a ha => List.mem_append_left _ ha).trans (k₂.mono i1)).trans (k₃.mono i2)

/-- The low words after a chunk. -/
theorem lows_rel {s s' : State} {n K : Nat} (hn : n ≤ K) (hK : K ≤ 64) {T : MSt} (hf : T.f % 2 = 1) (hI : Low K T s)
    {u v q r : BitVec 64} (hu : u = BitVec.ofInt 64 (msteps n (MSt.init T.d T.f T.g)).u)
    (hv : v = BitVec.ofInt 64 (msteps n (MSt.init T.d T.f T.g)).v)
    (hq : q = BitVec.ofInt 64 (msteps n (MSt.init T.d T.f T.g)).q)
    (hr : r = BitVec.ofInt 64 (msteps n (MSt.init T.d T.f T.g)).r)
    (h2 : s'.gpr .x2 = (s.gpr .x2 * u + s.gpr .x3 * v) >>> n)
    (h3 : s'.gpr .x3 = (s.gpr .x2 * q + s.gpr .x3 * r) >>> n)
    (hd : s'.gpr .x20 = half (msteps n (MSt.init T.d T.f T.g)).d) :
    Low (K - n) (msteps n T) s' := by
  obtain hmat := Divstep.msteps_mat (d := T.d) (g := T.g) hf n
  rw [Divstep.msteps_gen n T]
  refine ⟨hd, ?_, ?_⟩
  · rw [h2, hu, hv]; exact Divstep.low_upd hK hn hI.f hI.g hmat.1
  · rw [h3, hq, hr]; exact Divstep.low_upd hK hn hI.f hI.g hmat.2

theorem chunk0_ok (s : State) (hc : Consts s) {T : MSt} (hT : T.u = 1 ∧ T.v = 0 ∧ T.q = 0 ∧ T.r = 1)
    (hf : T.f % 2 = 1) (ho : T.d % 2 = 1) (hd : |T.d| + 30 < 2 ^ 62) (hI : Low 64 T s) :
    WP isa (.block chunk0) s fun s' =>
      Low 49 (msteps 15 T) s' ∧ Mat (msteps 15 T) s' ∧ Keeps chunkRegs s s' := by
  unfold chunk0
  rw [WP.block_append_iff]
  refine WP.mono (matrix_ok s (n := 15) (by decide) (by decide) hc hf ho (by push_cast; linarith) hI
    (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) fun s₁ ⟨d₁, M₁, k₁⟩ => ?_
  refine WP.mono (lows_ok s₁ (by decide) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) fun s₂ ⟨l₂, h₂, k₂⟩ => ⟨?_, ?_, ?_⟩
  · refine lows_rel (n := 15) (by decide) (by decide) hf hI M₁.u M₁.v M₁.q M₁.r ?_ ?_ ?_
    · rw [l₂, k₁.gpr .x2 (by decide), k₁.gpr .x3 (by decide)]
    · rw [h₂, k₁.gpr .x2 (by decide), k₁.gpr .x3 (by decide)]
    · rw [k₂.gpr _ (by decide), d₁]
  · rw [Divstep.msteps_gen 15 T]
    simp only [hT, mul_one, mul_zero, add_zero, zero_add]
    exact ⟨by rw [k₂.gpr _ (by decide)]; exact M₁.u, by rw [k₂.gpr _ (by decide)]; exact M₁.v,
      by rw [k₂.gpr _ (by decide)]; exact M₁.q, by rw [k₂.gpr _ (by decide)]; exact M₁.r⟩
  · exact (k₁.mono (by decide)).trans (k₂.mono (by decide))

/-- The composition of the matrices. -/
theorem compose_rel {s s' : State} {n : Nat} {T : MSt} {u v q r : Reg}
    (hM : Mat T s) (hC : ChunkMat (msteps n (MSt.init T.d T.f T.g)) u v q r s)
    (h4 : s'.gpr .x4 = s.gpr u * s.gpr .x4 + s.gpr v * s.gpr .x6)
    (h5 : s'.gpr .x5 = s.gpr u * s.gpr .x5 + s.gpr v * s.gpr .x7)
    (h6 : s'.gpr .x6 = s.gpr q * s.gpr .x4 + s.gpr r * s.gpr .x6)
    (h7 : s'.gpr .x7 = s.gpr q * s.gpr .x5 + s.gpr r * s.gpr .x7) : Mat (msteps n T) s' := by
  rw [Divstep.msteps_gen n T]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h4, hC.u, hC.v, hM.u, hM.q, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
  · rw [h5, hC.u, hC.v, hM.v, hM.r, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
  · rw [h6, hC.q, hC.r, hM.u, hM.q, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
  · rw [h7, hC.q, hC.r, hM.v, hM.r, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]

theorem chunk15_ok (s : State) (hc : Consts s) {K : Nat} (hK : 15 ≤ K ∧ K ≤ 64) {T : MSt}
    (hf : T.f % 2 = 1) (ho : T.d % 2 = 1) (hd : |T.d| + 30 < 2 ^ 62) (hI : Low K T s) (hM : Mat T s) :
    WP isa (.block chunk15) s fun s' =>
      Low (K - 15) (msteps 15 T) s' ∧ Mat (msteps 15 T) s' ∧ Keeps chunkRegs s s' := by
  unfold chunk15
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (matrix_ok s (n := 15) (by decide) hK.1 hc hf ho (by push_cast; linarith) hI
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))) fun s₁ ⟨d₁, M₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (lows_ok s₁ (by decide) (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))) fun s₂ ⟨l₂, h₂, k₂⟩ => ?_
  have C₂ : ChunkMat _ .x8 .x11 .x10 .x9 s₂ := ⟨by rw [k₂.gpr _ (by decide)]; exact M₁.u,
    by rw [k₂.gpr _ (by decide)]; exact M₁.v, by rw [k₂.gpr _ (by decide)]; exact M₁.q,
    by rw [k₂.gpr _ (by decide)]; exact M₁.r⟩
  have M₂ : Mat T s₂ := ⟨by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide)]; exact hM.u,
    by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide)]; exact hM.v,
    by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide)]; exact hM.q,
    by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide)]; exact hM.r⟩
  refine WP.mono (compose_ok s₂ (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) fun s₃ ⟨a, b, c, d, k₃⟩ =>
    ⟨?_, compose_rel M₂ C₂ a b c d, ?_⟩
  · refine lows_rel (n := 15) hK.1 hK.2 hf hI M₁.u M₁.v M₁.q M₁.r ?_ ?_ ?_
    · rw [k₃.gpr _ (by decide), l₂, k₁.gpr .x2 (by decide), k₁.gpr .x3 (by decide)]
    · rw [k₃.gpr _ (by decide), h₂, k₁.gpr .x2 (by decide), k₁.gpr .x3 (by decide)]
    · rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), d₁]
  · exact ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))

theorem chunk14_ok (s : State) (hc : Consts s) {K : Nat} (hK : 14 ≤ K) {T : MSt}
    (hf : T.f % 2 = 1) (ho : T.d % 2 = 1) (hd : |T.d| + 30 < 2 ^ 62) (hI : Low K T s) (hM : Mat T s) :
    WP isa (.block chunk14) s fun s' =>
      s'.gpr .x20 = half (msteps 14 T).d ∧ Mat (msteps 14 T) s' ∧ Keeps chunkRegs s s' := by
  unfold chunk14
  rw [WP.block_append_iff]
  refine WP.mono (matrix_ok s (n := 14) (by decide) hK hc hf ho (by push_cast; linarith) hI
    (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩))) fun s₁ ⟨d₁, M₁, k₁⟩ => ?_
  have M₂ : Mat T s₁ := ⟨by rw [k₁.gpr _ (by decide)]; exact hM.u, by rw [k₁.gpr _ (by decide)]; exact hM.v,
    by rw [k₁.gpr _ (by decide)]; exact hM.q, by rw [k₁.gpr _ (by decide)]; exact hM.r⟩
  refine WP.mono (compose_ok s₁ (Or.inr ⟨rfl, rfl, rfl, rfl⟩)) fun s₃ ⟨a, b, c, d, k₃⟩ =>
    ⟨?_, compose_rel M₂ M₁ a b c d, (k₁.mono (by decide)).trans (k₃.mono (by decide))⟩
  rw [k₃.gpr _ (by decide), d₁, Divstep.msteps_gen 14 T]

theorem Consts.of_keeps {s t : State} (h : Consts s) (k : Keeps chunkRegs s t) : Consts t :=
  ⟨by rw [k.gpr _ (by decide)]; exact h.c14, by rw [k.gpr _ (by decide)]; exact h.c15,
    by rw [k.gpr _ (by decide)]; exact h.c17⟩

/-- A batch's 59 divsteps, from `i` in `x20` and the low words of `f` and `g` in
`x2`, `x3`: `i` and the matrix in `x20`, `x4`–`x7`. -/
theorem words_ok (s : State) {d f g : Int} (hd : |d| ≤ 2 ^ 30) (ho : d % 2 = 1) (hf : f % 2 = 1)
    (h1 : s.gpr .x20 = half d) (h2 : ((s.gpr .x2).toNat : Int) % 2 ^ 64 = f % 2 ^ 64)
    (h3 : ((s.gpr .x3).toNat : Int) % 2 ^ 64 = g % 2 ^ 64) :
    WP isa (.block divsteps59) s fun t =>
      t.gpr .x20 = half (msteps 59 (MSt.init d f g)).d ∧ Mat (msteps 59 (MSt.init d f g)) t ∧ Keeps wordRegs s t := by
  obtain ⟨T0, hT0⟩ : ∃ T, T = MSt.init d f g := ⟨_, rfl⟩
  have f0 : T0.f % 2 = 1 := by rw [hT0]; exact hf
  have o0 : T0.d % 2 = 1 := by rw [hT0]; exact ho
  obtain odd : ∀ k, (msteps k T0).f % 2 = 1 := Divstep.msteps_f_odd f0
  obtain dodd : ∀ k, (msteps k T0).d % 2 = 1 := msteps_d_odd o0
  obtain dd : ∀ k ≤ 59, |(msteps k T0).d| + 30 < 2 ^ 62 := fun k hk => by
    have := Divstep.msteps_d T0 k
    rw [show T0.d = d by rw [hT0]; rfl] at this
    omega_using [this, hd, hk]
  rw [← hT0]
  simp only [divsteps59, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s) fun s₁ ⟨c₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chunk0_ok s₁ c₁ (T := T0) (by rw [hT0]; exact ⟨rfl, rfl, rfl, rfl⟩) f0 o0 (dd 0 (by decide))
    ⟨by rw [k₁.gpr _ (by decide), hT0]; exact h1, by rw [k₁.gpr _ (by decide), hT0]; exact h2,
      by rw [k₁.gpr _ (by decide), hT0]; exact h3⟩) fun s₂ ⟨L₂, M₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chunk15_ok s₂ (c₁.of_keeps k₂) (by decide) (odd 15) (dodd 15) (dd 15 (by decide)) L₂ M₂)
    fun s₃ ⟨L₃, M₃, k₃⟩ => ?_
  rw [← Divstep.msteps_add] at L₃ M₃
  rw [WP.block_append_iff]
  have c₃ := (c₁.of_keeps k₂).of_keeps k₃
  refine WP.mono (chunk15_ok s₃ c₃ (by decide) (odd 30) (dodd 30) (dd 30 (by decide)) L₃ M₃)
    fun s₄ ⟨L₄, M₄, k₄⟩ => ?_
  rw [← Divstep.msteps_add] at L₄ M₄
  refine WP.mono (chunk14_ok s₄ (c₃.of_keeps k₄) (by decide) (odd 45) (dodd 45) (dd 45 (by decide)) L₄ M₄)
    fun s₅ ⟨d₅, M₅, k₅⟩ => ?_
  rw [← Divstep.msteps_add] at d₅ M₅
  exact ⟨d₅, M₅, (k₁.mono (by decide)).trans ((((k₂.trans k₃).trans k₄).trans k₅).mono (by decide))⟩

end VG.Proof.Ed25519.AArch64.Divstep

/-! # The rows of the inversion's update

The blocks of a batch's update as arithmetic on the row (`row`, `x2`, `x3`,
`x8`–`x10`) and the operand (`opd`, `x11`–`x14`).
-/

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Divstep
open VG.Proof.Ed25519.AArch64 Word64
open VG.Proof.Mont.AArch64 (KeepRegs)

variable {large : Bool}

/-! ## Loads and stores -/

theorem ldp_ok {s : State} {base : Addr} (hs : Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d ≤ 504) {t1 t2 : Reg} (ht : t1 ≠ t2) :
    exec (.ldp t1 t2 .x0 d) s = some ((s.write .x t1 (word s.mem base d)).write .x t2
      (word s.mem base (d + 8))) := by
  have := workSize_ge large
  have e8 : (8 : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have h1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
    rw [hs.x0]
    exact ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) (by omega_using [hd, this])⟩
  have h2 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d + 8) 8 := by
    rw [hs.x0, e8, Offset.add_add]
    exact ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) (by omega_using [hd, this])⟩
  simp only [exec, ne_eq, ht, not_false_eq_true, ha, hd, and_self, ite_true, State.load, h1, h2,
    Option.bind_some, Option.map_some, BitVec.setWidth_eq]
  rw [hs.x0, e8, Offset.add_add]
  rfl

theorem stp_ok {s : State} {base : Addr} (hs : Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d ≤ 504) (t1 t2 : Reg) :
    exec (.stp t1 t2 .x0 d) s = some { s with
      mem := (s.mem.writeW (off base d) (s.gpr t1)).writeW (off base (d + 8)) (s.gpr t2) } := by
  have := workSize_ge large
  have e8 : (8 : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have h1 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
    rw [hs.x0]
    exact ⟨_, hs.wr, contains_scWith (large := large) (by omega_using [hd, this])⟩
  have h2 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d + 8) 8 := by
    rw [hs.x0, e8, Offset.add_add]
    exact ⟨_, hs.wr, contains_scWith (large := large) (by omega_using [hd, this])⟩
  simp only [exec, ha, hd, and_self, ite_true, State.store, h1, Option.bind_some, read_x, BitVec.setWidth_eq]
  simp only [h2]
  rw [hs.x0, e8, Offset.add_add]
  rfl

/-- Offsets of `ldp` and `stp`. -/
abbrev Off4 (o : Nat) : Prop := o % 8 = 0 ∧ o ≤ 488

theorem ldp4_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : Off4 o)
    {a b c d : Reg} (hd : ([a, b, c, d, .x0] : List Reg).Nodup) :
    WP isa (.block (ldp4 o a b c d)) s fun t =>
      t.gpr a = word s.mem base o ∧ t.gpr b = word s.mem base (o + 8) ∧
      t.gpr c = word s.mem base (o + 16) ∧ t.gpr d = word s.mem base (o + 24) ∧
      Keeps [a, b, c, d] s t := by
  obtain ⟨halign, hbound⟩ := ho
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hab, hac, had, ha0⟩, ⟨hbc, hbd, hb0⟩, ⟨hcd, hc0⟩, ⟨hd0, _⟩⟩ := hd
  apply WP.of_runBlock
  simp only [ldp4, runBlock_cons, runStep_some, runBlock_nil,
    ldp_ok hs halign (by omega_using [hbound]) hab,
    ldp_ok ((hs.write ha0 _).write hb0 _) (show (o + 16) % 8 = 0 by omega_using [halign]) (by omega_using [hbound]) hcd,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, had, hac, hab, ite_false, ite_true, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, hbd, hbc, ite_false, ite_true, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, hcd, ite_false, ite_true, BitVec.setWidth_eq, RegUpd.mem_write]
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.mem_write]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem stp4_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : Off4 o) (a b c d : Reg) :
    WP isa (.block (stp4 o a b c d)) s fun s' =>
      s' = { s with mem := st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) } := by
  obtain ⟨halign, hbound⟩ := ho
  apply WP.of_runBlock
  simp only [stp4, runBlock_cons, runStep_some, runBlock_nil,
    stp_ok hs halign (by omega_using [hbound]),
    stp_ok (hs.setMem _) (show (o + 16) % 8 = 0 by omega_using [halign]) (by omega_using [hbound]),
    Option.some.injEq, exists_eq_left']
  rfl

/-! ## The row and the operand -/

/-- The row's value. -/
def row (s : State) : Nat :=
  val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) + 2 ^ 256 * (s.gpr .x10).toNat

/-- The operand's value. -/
def opd (s : State) : Nat := val4 (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14)

/-- Its four low words'. -/
def lo (s : State) : Nat := val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9)

theorem lo_lt (s : State) : lo s < 2 ^ 256 := val4_lt _ _ _ _

theorem row_lt (s : State) : row s < 2 ^ 256 * 2 ^ 64 := by
  have := val4_lt (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9)
  have := (s.gpr .x10).isLt
  unfold row; omega_arith

theorem opd_lt (s : State) : opd s < 2 ^ 256 := val4_lt _ _ _ _

theorem opd_keeps {rs : List Reg} {s t : State} (k : Keeps rs s t) (h : .x11 ∉ rs ∧ .x12 ∉ rs ∧ .x13 ∉ rs ∧ .x14 ∉ rs) :
    opd t = opd s := by
  unfold opd; rw [k.gpr _ h.1, k.gpr _ h.2.1, k.gpr _ h.2.2.1, k.gpr _ h.2.2.2]

theorem row_keeps {rs : List Reg} {s t : State} (k : Keeps rs s t)
    (h : .x2 ∉ rs ∧ .x3 ∉ rs ∧ .x8 ∉ rs ∧ .x9 ∉ rs ∧ .x10 ∉ rs) : row t = row s := by
  unfold row
  rw [k.gpr _ h.1, k.gpr _ h.2.1, k.gpr _ h.2.2.1, k.gpr _ h.2.2.2.1, k.gpr _ h.2.2.2.2]

/-- The operand from memory. -/
theorem ldOpd_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : Off4 o) :
    WP isa (.block (ldp4 o .x11 .x12 .x13 .x14)) s fun t =>
      opd t = fe s.mem base o ∧ Keeps [.x11, .x12, .x13, .x14] s t :=
  WP.mono (ldp4_ok hs ho (by decide)) fun t ⟨a, b, c, d, k⟩ => ⟨by unfold opd; rw [a, b, c, d], k⟩

/-! ## Products -/

theorem mulFirst_arith {L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3 R1 R2 R3 R4 D1 D2 D3 D4 : Nat}
    (f1 : R1 + 2 ^ 64 * D1 = H0 + L1 + 0) (f2 : R2 + 2 ^ 64 * D2 = H1 + L2 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = H2 + L3 + D2) (f4 : R4 + 2 ^ 64 * D4 = H3 + 0 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3)
    (p0 : P0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p1 : P1 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p2 : P2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p3 : P3 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    L0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 =
      P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3 := by
  omega_using [f1, f2, f3, f4, m0, m1, m2, m3, p0, p1, p2, p3]

theorem mulFirst_value (a b0 b1 b2 b3 : Word) :
    let d1 := carryOut (mulHi a b0) (a * b1) false
    let d2 := carryOut (mulHi a b1) (a * b2) d1
    let d3 := carryOut (mulHi a b2) (a * b3) d2
    val4 (a * b0) (addCarry (mulHi a b0) (a * b1) false)
        (addCarry (mulHi a b1) (a * b2) d1) (addCarry (mulHi a b2) (a * b3) d2) +
        2 ^ 256 * (addCarry (mulHi a b3) 0 d3).toNat =
      a.toNat * val4 b0 b1 b2 b3 := by
  intro d1 d2 d3
  simp only [val4]
  rw [mul_val4]
  exact mulFirst_arith (addCarry_value (mulHi a b0) (a * b1) false)
    (addCarry_value (mulHi a b1) (a * b2) d1) (addCarry_value (mulHi a b2) (a * b3) d2)
    (addCarry_value (mulHi a b3) 0 d3)
    (mul_lo_hi a b0) (mul_lo_hi a b1) (mul_lo_hi a b2) (mul_lo_hi a b3)
    (mul_le a b0) (mul_le a b1) (mul_le a b2) (mul_le a b3)

/-- The registers the products write. -/
abbrev rowRegs : List Reg := [.x2, .x3, .x8, .x9, .x10, .x15]

/-- What the frame of a straight block of register arithmetic needs. -/
macro "row_frame" : tactic => `(tactic| plain_simp_names (
  exact ⟨by reg_keeps, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩))

theorem mulFirst_ok (s : State) {u : Reg} (hu : u = .x4 ∨ u = .x6) (hz : s.gpr .x16 = 0) :
    WP isa (.block (mulFirst u)) s fun t =>
      row t = (s.gpr u).toNat * opd s ∧ Keeps rowRegs s t := by
  have h := fun a => mulFirst_value a (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14)
  dsimp only [addCarry, carryOut, mulHi] at h
  apply WP.of_runBlock
  rcases hu with rfl | rfl <;>
  · simp only [mulFirst, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, ↓RegUpd.c_write, row, opd,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
    exact ⟨h _, by row_frame⟩

theorem mulAcc_arith {T0 T1 T2 T3 T4 L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3
    S0 S1 S2 S3 U R1 R2 R3 R4 C0 C1 C2 C3 C4 D1 D2 D3 D4 : Nat}
    (e0 : S0 + 2 ^ 64 * C0 = T0 + L0 + 0) (e1 : S1 + 2 ^ 64 * C1 = T1 + L1 + C0)
    (e2 : S2 + 2 ^ 64 * C2 = T2 + L2 + C1) (e3 : S3 + 2 ^ 64 * C3 = T3 + L3 + C2)
    (e4 : U + 2 ^ 64 * C4 = T4 + 0 + C3)
    (f1 : R1 + 2 ^ 64 * D1 = S1 + H0 + 0) (f2 : R2 + 2 ^ 64 * D2 = S2 + H1 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = S3 + H2 + D2) (f4 : R4 + 2 ^ 64 * D4 = U + H3 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3) :
    S0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 + 2 ^ 256 * 2 ^ 64 * (C4 + D4) =
      T0 + 2 ^ 64 * T1 + 2 ^ 128 * T2 + 2 ^ 192 * T3 + 2 ^ 256 * T4 +
        (P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3) := by
  omega_using [e0, e1, e2, e3, e4, f1, f2, f3, f4, m0, m1, m2, m3]

theorem mulAcc_value (a b0 b1 b2 b3 t0 t1 t2 t3 t4 : Word) :
    let c0 := carryOut t0 (a * b0) false
    let c1 := carryOut t1 (a * b1) c0
    let c2 := carryOut t2 (a * b2) c1
    let c3 := carryOut t3 (a * b3) c2
    let s1 := addCarry t1 (a * b1) c0
    let s2 := addCarry t2 (a * b2) c1
    let s3 := addCarry t3 (a * b3) c2
    let u := addCarry t4 0 c3
    let d1 := carryOut s1 (mulHi a b0) false
    let d2 := carryOut s2 (mulHi a b1) d1
    let d3 := carryOut s3 (mulHi a b2) d2
    ∃ k, val4 (addCarry t0 (a * b0) false) (addCarry s1 (mulHi a b0) false)
        (addCarry s2 (mulHi a b1) d1) (addCarry s3 (mulHi a b2) d2) +
        2 ^ 256 * (addCarry u (mulHi a b3) d3).toNat + 2 ^ 256 * 2 ^ 64 * k =
      val4 t0 t1 t2 t3 + 2 ^ 256 * t4.toNat + a.toNat * val4 b0 b1 b2 b3 := by
  intro c0 c1 c2 c3 s1 s2 s3 u d1 d2 d3
  simp only [val4]
  rw [mul_val4]
  exact ⟨_, mulAcc_arith (addCarry_value t0 (a * b0) false) (addCarry_value t1 (a * b1) c0)
    (addCarry_value t2 (a * b2) c1) (addCarry_value t3 (a * b3) c2) (addCarry_value t4 0 c3)
    (addCarry_value s1 (mulHi a b0) false) (addCarry_value s2 (mulHi a b1) d1)
    (addCarry_value s3 (mulHi a b2) d2) (addCarry_value u (mulHi a b3) d3)
    (mul_lo_hi a b0) (mul_lo_hi a b1) (mul_lo_hi a b2) (mul_lo_hi a b3)⟩

theorem mulAcc_ok (s : State) {v : Reg} (hv : v = .x5 ∨ v = .x7) (hz : s.gpr .x16 = 0) :
    WP isa (.block (mulAcc v)) s fun t =>
      (∃ k, row t + 2 ^ 256 * 2 ^ 64 * k = row s + (s.gpr v).toNat * opd s) ∧ Keeps rowRegs s t := by
  have h := fun a => mulAcc_value a (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x2) (s.gpr .x3)
    (s.gpr .x8) (s.gpr .x9) (s.gpr .x10)
  dsimp only [addCarry, carryOut, mulHi] at h
  apply WP.of_runBlock
  rcases hv with rfl | rfl <;>
  · simp only [mulAcc, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, ↓RegUpd.c_write, row, opd,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
    exact ⟨h _, by row_frame⟩

/-! ## Signs -/

/-- Four words' value in two's complement. -/
def sv (X : Nat) : Int := if X < 2 ^ 255 then X else X - 2 ^ 256

theorem opd_msb (s : State) : (s.gpr .x14).msb = decide (2 ^ 255 ≤ opd s) := by
  have := (s.gpr .x11).isLt; have := (s.gpr .x12).isLt; have := (s.gpr .x13).isLt; have := (s.gpr .x14).isLt
  rw [BitVec.msb_eq_decide]
  apply decide_eq_decide.mpr
  unfold opd val4
  constructor <;> intro <;> omega_arith

theorem signed_ok (s : State) {u : Reg} (hu : u ∈ [Reg.x4, .x5, .x6, .x7]) (hz : s.gpr .x16 = 0) :
    WP isa (.block (signed u)) s fun t =>
      (∃ k, row t + 2 ^ 256 * (if 2 ^ 255 ≤ opd s then (s.gpr u).toNat else 0) = row s + 2 ^ 256 * 2 ^ 64 * k) ∧
      Keeps [.x10, .x15] s t := by
  have hm := opd_msb s
  apply WP.of_runBlock
  have fin : ∀ w : Word, w = (if (s.gpr .x14).msb = true then s.gpr u else 0) →
      ∃ k, val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) + 2 ^ 256 * (s.gpr .x10 - w).toNat +
        2 ^ 256 * (if 2 ^ 255 ≤ opd s then (s.gpr u).toNat else 0) =
      val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) + 2 ^ 256 * (s.gpr .x10).toNat + 2 ^ 256 * 2 ^ 64 * k := by
    intro w hw
    have e : (if 2 ^ 255 ≤ opd s then (s.gpr u).toNat else 0) = w.toNat := by
      rw [hw, hm]
      by_cases h : 2 ^ 255 ≤ opd s
      · simp only [h, decide_true, ↓reduceIte]
      · simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]; rfl
    rw [e, BitVec.toNat_sub]
    have h1 := w.isLt
    have h2 := (s.gpr .x10).isLt
    generalize val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) = V
    generalize (s.gpr .x10).toNat = x at *
    generalize w.toNat = y at *
    by_cases h : y ≤ x
    · exact ⟨0, by omega_using [h1, h2, h]⟩
    · exact ⟨1, by omega_using [h1, h2, h]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
  · simp only [signed, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, CondCode.holds,
      ↓RegUpd.gpr_write, row, BitVec.and_self,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
    refine ⟨fin _ rfl, ?_, rfl, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## Sums, differences and shifts -/

theorem addOpd_ok (s : State) :
    WP isa (.block addOpd) s fun t =>
      (∃ k, lo t + 2 ^ 256 * k = lo s + opd s) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  have h := add4_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) (s.gpr .x11) (s.gpr .x12) (s.gpr .x13)
    (s.gpr .x14) false
  dsimp only [addCarry, carryOut] at h
  apply WP.of_runBlock
  simp only [addOpd, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, opd,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨⟨_, h⟩, by row_frame⟩

theorem subOpd_ok (s : State) :
    WP isa (.block subOpd) s fun t =>
      (∃ k, lo t + opd s = lo s + 2 ^ 256 * k) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  have h := sub4_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) (s.gpr .x11) (s.gpr .x12) (s.gpr .x13)
    (s.gpr .x14) true
  dsimp only [addCarry, carryOut] at h
  apply WP.of_runBlock
  simp only [subOpd, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, opd,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨⟨_, h⟩, by row_frame⟩

theorem shift_arith {t0 t1 t2 t3 t4 : Nat} (h4 : t4 < 2 ^ 64) :
    (t0 / 2 ^ 59 + 2 ^ 5 * (t1 % 2 ^ 59)) + 2 ^ 64 * (t1 / 2 ^ 59 + 2 ^ 5 * (t2 % 2 ^ 59)) +
      2 ^ 128 * (t2 / 2 ^ 59 + 2 ^ 5 * (t3 % 2 ^ 59)) + 2 ^ 192 * (t3 / 2 ^ 59 + 2 ^ 5 * (t4 % 2 ^ 59)) +
      2 ^ 256 * (t4 / 2 ^ 59) =
    (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 + 2 ^ 256 * t4) / 2 ^ 59 := by
  omega_using [h4]

theorem shift_ok (s : State) :
    WP isa (.block shift) s fun t =>
      (∃ k, lo t + 2 ^ 256 * k = row s / 2 ^ 59) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  apply WP.of_runBlock
  simp only [shift, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, lo, row, show 59 < Size.x.bits from by decide, val4,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨(s.gpr .x10).toNat / 2 ^ 59, ?_⟩, by row_frame⟩
  rw [← shift_arith (s.gpr .x10).isLt]
  dsimp only [Size.bits]
  rw [Divstep.extr59, Divstep.extr59, Divstep.extr59, Divstep.extr59]

/-! ## The offset of `a` and `b`'s rows -/

theorem twoP_ok (s : State) (hz : s.gpr .x16 = 0) :
    WP isa (.block twoP) s fun t =>
      t.gpr .x15 = BitVec.ofNat 64 (2 ^ 64 - 38) ∧ t.gpr .x17 = BitVec.ofNat 64 (2 ^ 64 - 1) ∧
      Keeps [.x15, .x17] s t := by
  apply WP.of_runBlock
  simp only [twoP, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, show 16 * 0 < Size.x.bits from by decide, show (1 : Nat) < 4096 from by decide, hz,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨by decide, by decide, by row_frame⟩

/-- `2 p` less a number at most `2 p`. -/
theorem negRow_ok (s : State) (h15 : s.gpr .x15 = BitVec.ofNat 64 (2 ^ 64 - 38))
    (h17 : s.gpr .x17 = BitVec.ofNat 64 (2 ^ 64 - 1)) (h : lo s ≤ 2 ^ 256 - 38) :
    WP isa (.block negRow) s fun t =>
      lo t + lo s = 2 ^ 256 - 38 ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  have e := sub4_value (s.gpr .x15) (s.gpr .x17) (s.gpr .x17) (s.gpr .x17)
    (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) true
  have c : val4 (s.gpr .x15) (s.gpr .x17) (s.gpr .x17) (s.gpr .x17) = 2 ^ 256 - 38 := by rw [h15, h17]; decide
  rw [c] at e
  dsimp only [addCarry, carryOut] at e
  have run : WP isa (.block negRow) s fun t =>
      (∃ k, lo t + lo s = 2 ^ 256 - 38 + 2 ^ 256 * k) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
    apply WP.of_runBlock
    simp only [negRow, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
    exact ⟨⟨_, e⟩, by row_frame⟩
  refine WP.mono run fun t ⟨⟨k, hk⟩, kt⟩ => ⟨?_, kt⟩
  have := lo_lt t
  omega_using [hk, this, h]

theorem extr5 (s0 s1 : BitVec 64) :
    ((s1 ++ s0).extractLsb' 5 64).toNat = s0.toNat / 2 ^ 5 + 2 ^ 59 * (s1.toNat % 2 ^ 5) := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt s0.isLt, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := s0.isLt; have := s1.isLt
  omega_using []

theorem lsl59 (w : BitVec 64) : (w <<< 59).toNat = 2 ^ 59 * (w.toNat % 2 ^ 5) := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_using []

/-- The five words of `x11`–`x15`. -/
def off5 (s : State) : Nat := opd s + 2 ^ 256 * (s.gpr .x15).toNat

theorem subShift_arith {d0 d1 d2 d3 d4 L O k : Nat}
    (e : d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + O + (1 - true.toNat) = L + 2 ^ 256 * k) (hk : k ≤ 1)
    (h4 : d4 = (2 ^ 64 - 1) * k) :
    2 ^ 59 * (d0 % 2 ^ 5) + 2 ^ 64 * (d0 / 2 ^ 5 + 2 ^ 59 * (d1 % 2 ^ 5)) +
      2 ^ 128 * (d1 / 2 ^ 5 + 2 ^ 59 * (d2 % 2 ^ 5)) + 2 ^ 192 * (d2 / 2 ^ 5 + 2 ^ 59 * (d3 % 2 ^ 5)) +
      2 ^ 256 * (d3 / 2 ^ 5 + 2 ^ 59 * (d4 % 2 ^ 5)) + 2 ^ 59 * O = 2 ^ 59 * L + 2 ^ 256 * 2 ^ 64 * k := by
  have e : d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + O = L + 2 ^ 256 * k := e
  omega_using [e, hk, h4]

theorem subShift_value (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let c0 := carryOut a0 (~~~b0) true
    let c1 := carryOut a1 (~~~b1) c0
    let c2 := carryOut a2 (~~~b2) c1
    let c3 := carryOut a3 (~~~b3) c2
    let d0 := addCarry a0 (~~~b0) true
    let d1 := addCarry a1 (~~~b1) c0
    let d2 := addCarry a2 (~~~b2) c1
    let d3 := addCarry a3 (~~~b3) c2
    let d4 := addCarry 0 (~~~0) c3
    ∃ k, val4 (d0 <<< 59) ((d1 ++ d0).extractLsb' 5 64) ((d2 ++ d1).extractLsb' 5 64) ((d3 ++ d2).extractLsb' 5 64) +
      2 ^ 256 * ((d4 ++ d3).extractLsb' 5 64).toNat + 2 ^ 59 * val4 b0 b1 b2 b3 =
        2 ^ 59 * val4 a0 a1 a2 a3 + 2 ^ 256 * 2 ^ 64 * k := by
  intro c0 c1 c2 c3 d0 d1 d2 d3 d4
  have e : val4 d0 d1 d2 d3 + val4 b0 b1 b2 b3 + (1 - true.toNat) = val4 a0 a1 a2 a3 + 2 ^ 256 * (1 - c3.toNat) :=
    sub4_value a0 a1 a2 a3 b0 b1 b2 b3 true
  have m : d4.toNat = (2 ^ 64 - 1) * (1 - c3.toNat) := by
    show (addCarry 0 (~~~0) c3).toNat = _
    cases c3 <;> decide
  refine ⟨1 - c3.toNat, ?_⟩
  simp only [val4]
  rw [extr5, extr5, extr5, extr5, lsl59]
  exact subShift_arith e (Nat.sub_le _ _) m

theorem subShift_ok (s : State) (hz : s.gpr .x16 = 0) :
    WP isa (.block subShift) s fun t =>
      (∃ k, off5 t + 2 ^ 59 * opd s = 2 ^ 59 * lo s + 2 ^ 256 * 2 ^ 64 * k) ∧ t.gpr .x17 = 19 ∧
      Keeps [.x2, .x3, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x17] s t := by
  have e := subShift_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) (s.gpr .x11) (s.gpr .x12) (s.gpr .x13)
    (s.gpr .x14)
  dsimp only [addCarry, carryOut] at e
  apply WP.of_runBlock
  simp only [subShift, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, off5, opd,
    show 59 < Size.x.bits from by decide, show 5 < Size.x.bits from by decide,
    show 16 * 0 < Size.x.bits from by decide, hz,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨e, by decide, by row_frame⟩

/-! ## The fold -/

theorem fold_arith {t0 t1 t2 t3 t4 e0 e1 e2 e3 e4 r0 r1 r2 r3 r4 c0 c1 c2 c3 c4 : Nat}
    {y cy h ch x9 l k P s0 s1 s2 s3 d0 d1 d2 d3 W K : Nat}
    (a0 : r0 + 2 ^ 64 * c0 = t0 + e0 + 0) (a1 : r1 + 2 ^ 64 * c1 = t1 + e1 + c0)
    (a2 : r2 + 2 ^ 64 * c2 = t2 + e2 + c1) (a3 : r3 + 2 ^ 64 * c3 = t3 + e3 + c2)
    (a4 : r4 + 2 ^ 64 * c4 = t4 + e4 + c3)
    (lr0 : r0 < 2 ^ 64) (lr1 : r1 < 2 ^ 64) (lr2 : r2 < 2 ^ 64) (lr3 : r3 < 2 ^ 64) (lr4 : r4 < 2 ^ 64)
    (b0 : y + 2 ^ 64 * cy = r3 + r3 + 0) (ly : y < 2 ^ 64) (b1 : h + 2 ^ 64 * ch = r4 + r4 + cy)
    (b2 : x9 = y / 2)
    (mk : l + 2 ^ 64 * k = P) (hP : P = h * 19)
    (d0e : s0 + 2 ^ 64 * d0 = r0 + l + 0) (d1e : s1 + 2 ^ 64 * d1 = r1 + k + d0)
    (d2e : s2 + 2 ^ 64 * d2 = r2 + 0 + d1) (d3e : s3 + 2 ^ 64 * d3 = x9 + 0 + d2)
    (hW : t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 + 2 ^ 256 * t4 +
      (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3 + 2 ^ 256 * e4) = W + 2 ^ 256 * 2 ^ 64 * K)
    (lW : W < 2 ^ 256 * 2 ^ 61) :
    s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3 = W % 2 ^ 255 + 19 * (W / 2 ^ 255) := by
  have lk : k < 2 ^ 64 := by omega_using [mk, hP, b1, lr4, b0, lr3, ly]
  have eW : W = r0 + 2 ^ 64 * r1 + 2 ^ 128 * r2 + 2 ^ 192 * r3 + 2 ^ 256 * r4 := by
    omega_using [a0, a1, a2, a3, a4, lr0, lr1, lr2, lr3, lr4, hW, lW]
  have l4 : r4 < 2 ^ 61 := by omega_using [eW, lW]
  have eh : h = 2 * r4 + cy := by omega_using [b1, l4, b0, lr3]
  have e3 : x9 + 2 ^ 63 * cy = r3 := by omega_using [b0, b2, ly]
  have lx : x9 < 2 ^ 63 := by omega_using [b2, ly]
  have q : W / 2 ^ 255 = h := by
    rw [eW, ← e3, eh]; omega_using [lr0, lr1, lr2, lx]
  have m : W % 2 ^ 255 = r0 + 2 ^ 64 * r1 + 2 ^ 128 * r2 + 2 ^ 192 * x9 := by
    rw [eW, ← e3]; omega_using [lr0, lr1, lr2, lx]
  rw [q, m]
  omega_using [d0e, d1e, d2e, d3e, mk, hP, eh, l4, lx, lr0, lr1, lr2, b0, lr3]

theorem lsr1 (w : BitVec 64) : (w >>> 1).toNat = w.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem fold_ok (s : State) (hz : s.gpr .x16 = 0) (h17 : s.gpr .x17 = 19) {W K : Nat}
    (hW : row s + off5 s = W + 2 ^ 256 * 2 ^ 64 * K) (lW : W < 2 ^ 256 * 2 ^ 61) :
    WP isa (.block fold) s fun t =>
      lo t = W % 2 ^ 255 + 19 * (W / 2 ^ 255) ∧ Keeps [.x2, .x3, .x8, .x9, .x10, .x11, .x12] s t := by
  apply WP.of_runBlock
  simp only [fold, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, val4,
    show 1 < Size.x.bits from by decide, hz,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by row_frame⟩
  dsimp only [Size.bits]
  refine fold_arith (addCarry_value (s.gpr .x2) (s.gpr .x11) false) (addCarry_value (s.gpr .x3) (s.gpr .x12) _)
    (addCarry_value (s.gpr .x8) (s.gpr .x13) _) (addCarry_value (s.gpr .x9) (s.gpr .x14) _)
    (addCarry_value (s.gpr .x10) (s.gpr .x15) _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (addCarry_value _ _ false) (BitVec.isLt _) (addCarry_value _ _ _) (lsr1 _)
    (mul_lo_hi _ _) (by rw [h17]; rfl) (addCarry_value _ _ false) (addCarry_value _ _ _) (addCarry_value _ _ _)
    (addCarry_value _ _ _) hW lW

end VG.Proof.Ed25519.AArch64.Divstep

/-! # The inversion's update

`(f, g)` after a batch's update (`updateFG_ok`), and `(a, b)` modulo `p` (`updateAB_ok`).
-/

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

/-! # The ends of the inversion

`start` sets `f = p`, `a = 0`, `b = 2^-590` and `g` to the input modulo `p`
(`start_ok`); `finish` leaves `a` or `2 p - a` in slot 15 (`finish_ok`).
-/

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Divstep
open VG.Proof.Ed25519.AArch64 Word64
open VG.Proof.Mont.AArch64 (KeepRegs)

variable {large : Bool}

theorem Scr.setFrame {rs : List Reg} {s s' : State} (k : Keeps rs s s') {m : Mem} {t : State}
    (ht : t = { s' with mem := m }) : KeepRegs rs s t :=
  ⟨fun r hr => by rw [ht]; exact k.gpr r hr, by rw [ht]; exact k.rd, by rw [ht]; exact k.wr, by rw [ht]; exact k.sp⟩

theorem set4_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : Off4 o) {v : Nat}
    (hv : v < 2 ^ 256) :
    WP isa (.block (set4 o v)) s fun t =>
      fe t.mem base o = v ∧ Outside base o 32 s.mem t.mem ∧ KeepRegs updRegs s t := by
  simp only [set4, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s _ _) fun s₁ ⟨v₁, q₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₁ _ _) fun s₂ ⟨v₂, q₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₂ _ _) fun s₃ ⟨v₃, q₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₃ _ _) fun s₄ ⟨v₄, q₄⟩ => ?_
  have k : Keeps updRegs s s₄ := (((q₁.mono (by decide)).trans (q₂.mono (by decide))).trans
    (q₃.mono (by decide))).trans (q₄.mono (by decide))
  refine WP.mono (stp4_ok (hs.of_keeps k (by decide)) ho _ _ _ _) fun t ht => ⟨?_, ?_, Scr.setFrame k ht⟩
  · rw [ht]
    refine (fe_st4 _ _ (by omega_using [ho.2]) _ _ _ _).trans ?_
    rw [v₄, q₄.gpr .x8 (by decide), v₃, q₄.gpr .x3 (by decide), q₃.gpr .x3 (by decide), v₂, q₄.gpr .x2 (by decide),
      q₃.gpr .x2 (by decide), q₂.gpr .x2 (by decide), v₁]
    simp only [val4, BitVec.toNat_ofNat]
    omega_using [hv]
  · rw [ht, ← k.mem]; exact st4_outside _ _ (by omega_using [ho.2]) _ _ _ _

theorem foldTop_arith {t0 t1 t2 t3 y c w x9 s0 s1 s2 s3 d0 d1 d2 d3 : Nat}
    (l0 : t0 < 2 ^ 64) (l1 : t1 < 2 ^ 64) (l2 : t2 < 2 ^ 64) (l3 : t3 < 2 ^ 64)
    (b0 : y + 2 ^ 64 * c = t3 + t3 + 0) (ly : y < 2 ^ 64) (hx : x9 = y / 2) (hw : w = 19 * c)
    (d0e : s0 + 2 ^ 64 * d0 = t0 + w + 0) (d1e : s1 + 2 ^ 64 * d1 = t1 + 0 + d0)
    (d2e : s2 + 2 ^ 64 * d2 = t2 + 0 + d1) (d3e : s3 + 2 ^ 64 * d3 = x9 + 0 + d2) :
    s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3 =
      (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) % 2 ^ 255 +
        19 * ((t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) / 2 ^ 255) := by
  have e : x9 + 2 ^ 63 * c = t3 := by omega_using [b0, hx, ly]
  have lx : x9 < 2 ^ 63 := by omega_using [hx, ly]
  have q : (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) / 2 ^ 255 = c := by
    rw [← e]; omega_using [l0, l1, l2, lx]
  have m : (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) % 2 ^ 255 =
      t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * x9 := by
    rw [← e]; omega_using [l0, l1, l2, lx]
  rw [q, m]
  have hc : c ≤ 1 := by omega_using [b0, l3]
  omega_using [d0e, d1e, d2e, d3e, hw, lx, l0, l1, l2, hc]

theorem foldTop_ok (s : State) :
    WP isa (.block foldTop) s fun t =>
      lo t = lo s % 2 ^ 255 + 19 * (lo s / 2 ^ 255) ∧ t.gpr .x16 = 0 ∧ t.gpr .x17 = 19 ∧
      Keeps [.x2, .x3, .x8, .x9, .x11, .x16, .x17] s t := by
  have hw (c : Bool) : (if c = true then BitVec.setWidth 64 19#16 <<< (16 * 0) else
      BitVec.setWidth 64 0#16 <<< (16 * 0)).toNat = 19 * c.toNat := by cases c <;> decide
  apply WP.of_runBlock
  simp only [foldTop, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, RegUpd.c_write, lo, val4,
    show 1 < Size.x.bits from by decide, show 16 * 0 < Size.x.bits from by decide,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by decide, by decide, by row_frame⟩
  dsimp only [Size.bits]
  exact foldTop_arith (s.gpr .x2).isLt (s.gpr .x3).isLt (s.gpr .x8).isLt (s.gpr .x9).isLt
    (addCarry_value (s.gpr .x9) (s.gpr .x9) false) (BitVec.isLt _) (lsr1 _) (hw _)
    (addCarry_value _ _ false) (addCarry_value _ _ _) (addCarry_value _ _ _) (addCarry_value _ _ _)

theorem plus19_ok (s : State) (hz : s.gpr .x16 = 0) (h17 : s.gpr .x17 = 19) (h : lo s < 2 ^ 255 + 19) :
    WP isa (.block plus19) s fun t =>
      opd t = lo s + 19 ∧ Keeps [.x11, .x12, .x13, .x14] s t := by
  have e := add4_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) 19 0 0 0 false
  dsimp only [addCarry, carryOut] at e
  have c : val4 (19 : Word) 0 0 0 = 19 := by decide
  rw [c] at e
  have run : WP isa (.block plus19) s fun t =>
      (∃ k, opd t + 2 ^ 256 * k = lo s + 19) ∧ Keeps [.x11, .x12, .x13, .x14] s t := by
    apply WP.of_runBlock
    simp only [plus19, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, opd, hz, h17,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
    exact ⟨⟨_, e⟩, by row_frame⟩
  refine WP.mono run fun t ⟨⟨k, hk⟩, kt⟩ => ⟨?_, kt⟩
  have := opd_lt t
  omega_using [hk, this, h]

theorem reduceOnce_ok (s : State) :
    WP isa (.block reduceOnce) s fun t =>
      lo t = (if 2 ^ 255 ≤ opd s then opd s - 2 ^ 255 else lo s) ∧ Keeps [.x2, .x3, .x8, .x9, .x14] s t := by
  have hm := opd_msb s
  have hsh : ((s.gpr .x14 + s.gpr .x14) >>> 1).toNat = (s.gpr .x14).toNat % 2 ^ 63 := by
    rw [lsr1, BitVec.toNat_add]; omega_using []
  apply WP.of_runBlock
  simp only [reduceOnce, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, CondCode.holds,
    ↓RegUpd.gpr_write, lo, BitVec.and_self, show 1 < Size.x.bits from by decide, RegUpd.nf_write, hm,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · by_cases h : 2 ^ 255 ≤ opd s
    · simp only [h, decide_true, ↓reduceIte, val4]
      rw [hsh]
      unfold opd val4 at h ⊢
      have := (s.gpr .x11).isLt; have := (s.gpr .x12).isLt; have := (s.gpr .x13).isLt; have := (s.gpr .x14).isLt
      omega_arith
    · simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem bySign_ok (s : State) :
    WP isa (.block bySign) s fun t =>
      lo t = (if (s.gpr .x10).msb = true then lo s else opd s) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  apply WP.of_runBlock
  simp only [bySign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, CondCode.holds,
    ↓RegUpd.gpr_write, lo, opd, BitVec.and_self, RegUpd.nf_write,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨by cases (s.gpr .x10).msb <;> rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The registers the inversion writes. -/
abbrev invRegs : List Reg :=
  [.x20, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19]

theorem counters_ok (s : State) :
    WP isa (.block counters) s fun t => t.gpr .x20 = 0 ∧ t.gpr .x19 = BitVec.ofNat 64 10 ∧ Keeps [.x20, .x19] s t := by
  apply WP.of_runBlock
  simp only [counters, runBlock_cons, runStep_some, runBlock_nil, exec,
    ↓RegUpd.gpr_write, show 16 * 0 < Size.x.bits from by decide,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨by decide, by decide, by row_frame⟩

theorem start_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block start) s fun t =>
      fe t.mem base oF = Spec.X25519.P ∧ fe t.mem base oA = 0 ∧ fe t.mem base oB = b0 ∧
      fe t.mem base oG = fe s.mem base 128 % Spec.X25519.P ∧
      t.gpr .x20 = 0 ∧ t.gpr .x19 = BitVec.ofNat 64 10 ∧
      Outside base 192 512 s.mem t.mem ∧ KeepRegs invRegs s t := by
  simp only [start, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (set4_ok hs (o := oF) (by decide) (by decide)) fun s₁ ⟨v₁, o₁, k₁⟩ => ?_
  have hs₁ := Scr.of_keepRegs' hs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (set4_ok hs₁ (o := oA) (by decide) (by decide)) fun s₂ ⟨v₂, o₂, k₂'⟩ => ?_
  have k₂ := k₁.trans k₂'
  have hs₂ := Scr.of_keepRegs' hs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (set4_ok hs₂ (o := oB) (by decide) (by decide)) fun s₃ ⟨v₃, o₃, k₃'⟩ => ?_
  have k₃ := k₂.trans k₃'
  have hs₃ := Scr.of_keepRegs' hs k₃ (by decide)
  have X : fe s₃.mem base 128 = fe s.mem base 128 := by
    rw [o₃.fe (by decide) (by decide), o₂.fe (by decide) (by decide), o₁.fe (by decide) (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (ldp4_ok hs₃ (o := 128) (by decide) (by decide)) fun s₄ ⟨a, b, c, d, q₄⟩ => ?_
  have l₄ : lo s₄ = fe s.mem base 128 := by rw [← X]; unfold lo; rw [a, b, c, d]
  rw [WP.block_append_iff]
  refine WP.mono (foldTop_ok s₄) fun s₅ ⟨v₅, c16, c17, q₅⟩ => ?_
  rw [l₄] at v₅
  have hl : fe s.mem base 128 < 2 ^ 256 := val4_lt _ _ _ _
  have b₅ : lo s₅ < 2 ^ 255 + 19 := by rw [v₅]; omega_using [hl]
  rw [WP.block_append_iff]
  refine WP.mono (plus19_ok s₅ c16 c17 b₅) fun s₆ ⟨v₆, q₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceOnce_ok s₆) fun s₇ ⟨v₇, q₇⟩ => ?_
  have l₆ : lo s₆ = lo s₅ := by
    unfold lo; rw [q₆.gpr _ (by decide), q₆.gpr _ (by decide), q₆.gpr _ (by decide), q₆.gpr _ (by decide)]
  rw [l₆, v₆] at v₇
  have v₇' : lo s₇ = fe s.mem base 128 % Spec.X25519.P := by
    rw [v₇, show Spec.X25519.P = 2 ^ 255 - 19 from rfl]
    generalize fe s.mem base 128 = X at *
    generalize lo s₅ = Y at *
    split <;> omega_using [v₅, hl, b₅, ‹_›]
  have q : Keeps invRegs s₃ s₇ := (((q₄.mono (by decide)).trans (q₅.mono (by decide))).trans
    (q₆.mono (by decide))).trans (q₇.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (stp4_ok (hs₃.of_keeps q (by decide)) (o := oG) (by decide) _ _ _ _) fun s₈ h₈ => ?_
  have k₈ := (k₃.mono (by decide)).trans (Scr.setFrame q h₈)
  have o₈ : Outside base oG 32 s₃.mem s₈.mem := by
    rw [h₈, ← q.mem]; exact st4_outside _ _ (by decide) _ _ _ _
  refine WP.mono (counters_ok s₈) fun t ⟨c20, c19, q₉⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, c20, c19, ?_, ?_⟩
  · rw [q₉.mem, o₈.fe (by decide) (by decide), o₃.fe (by decide) (by decide), o₂.fe (by decide) (by decide), v₁]
  · rw [q₉.mem, o₈.fe (by decide) (by decide), o₃.fe (by decide) (by decide), v₂]
  · rw [q₉.mem, o₈.fe (by decide) (by decide), v₃]
  · rw [q₉.mem, h₈, fe_st4 _ _ (by decide)]; exact v₇'
  · rw [q₉.mem]
    exact (((o₁.mono (by decide) (by decide)).trans (o₂.mono (by decide) (by decide))).trans
      (o₃.mono (by decide) (by decide))).trans (o₈.mono (by decide) (by decide))
  · exact k₈.trans ⟨fun r hr => q₉.gpr r fun h => hr ((by decide : ∀ a ∈ ([.x20, .x19] : List Reg), a ∈ invRegs) r h),
      q₉.rd, q₉.wr, q₉.sp⟩

theorem finish_ok {s : State} {base : Addr} (hs : Scr s base large) (hA : fe s.mem base oA < abMax) :
    WP isa (.block finish) s fun t =>
      fe t.mem base 544 = (if 2 ^ 255 ≤ fe s.mem base oF then 2 ^ 256 - 38 - fe s.mem base oA else fe s.mem base oA) ∧
      Outside base 192 512 s.mem t.mem ∧ KeepRegs invRegs s t := by
  have hc := workSize_ge large
  simp only [finish, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldp4_ok hs (o := oA) (by decide) (by decide)) fun s₁ ⟨a, b, c, d, q₁⟩ => ?_
  have k₁ : Keeps invRegs s s₁ := q₁.mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok (hs.of_keeps k₁ (by decide)) (o := oA) (by decide)) fun s₂ ⟨v₂, q₂⟩ => ?_
  have k₂ : Keeps invRegs s s₂ := k₁.trans (q₂.mono (by decide))
  have l₁ : lo s₁ = fe s.mem base oA := by unfold lo; rw [a, b, c, d]
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs.of_keeps k₂ (by decide)) (d := oF + 24) (by decide) (by unfold oF; omega_using [hc]) .x10)
    fun s₃ ⟨v₃, q₃⟩ => ?_
  have k₃ : Keeps invRegs s s₃ := k₂.trans (q₃.mono (by decide))
  rw [WP.block_append_iff]
  have z : WP isa (.block ([.movz .x .x16 0 0] : List Instr)) s₃ fun t => t.gpr .x16 = 0 ∧ Keeps [.x16] s₃ t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      ↓RegUpd.gpr_write, show 16 * 0 < Size.x.bits from by decide,
      ↓reduceIte, Option.some.injEq, exists_eq_left']
    exact ⟨by decide, by row_frame⟩
  refine WP.mono z fun s₄ ⟨c16, q₄⟩ => ?_
  have k₄ : Keeps invRegs s s₄ := k₃.trans (q₄.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (twoP_ok s₄ c16) fun s₅ ⟨c15, c17, q₅⟩ => ?_
  have k₅ : Keeps invRegs s s₅ := k₄.trans (q₅.mono (by decide))
  have l₅ : lo s₅ = fe s.mem base oA := by
    rw [← l₁]; unfold lo
    rw [q₅.gpr _ (by decide), q₅.gpr _ (by decide), q₅.gpr _ (by decide), q₅.gpr _ (by decide),
      q₄.gpr _ (by decide), q₄.gpr _ (by decide), q₄.gpr _ (by decide), q₄.gpr _ (by decide),
      q₃.gpr _ (by decide), q₃.gpr _ (by decide), q₃.gpr _ (by decide), q₃.gpr _ (by decide),
      q₂.gpr _ (by decide), q₂.gpr _ (by decide), q₂.gpr _ (by decide), q₂.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (negRow_ok s₅ c15 c17 (by rw [l₅]; unfold abMax at hA; omega_using [hA])) fun s₆ ⟨v₆, q₆⟩ => ?_
  have k₆ : Keeps invRegs s s₆ := k₅.trans (q₆.mono (by decide))
  rw [l₅] at v₆
  have p₆ : opd s₆ = fe s.mem base oA := by
    rw [opd_keeps q₆ (by decide), opd_keeps q₅ (by decide), opd_keeps q₄ (by decide), opd_keeps q₃ (by decide), v₂,
      k₁.mem]
  have w₆ : s₆.gpr .x10 = word s.mem base (oF + 24) := by
    rw [q₆.gpr _ (by decide), q₅.gpr _ (by decide), q₄.gpr _ (by decide), v₃, k₂.mem]
  rw [WP.block_append_iff]
  refine WP.mono (bySign_ok s₆) fun s₇ ⟨v₇, q₇⟩ => ?_
  have k₇ : Keeps invRegs s s₇ := k₆.trans (q₇.mono (by decide))
  have hsl : offset 15 = 544 := rfl
  refine WP.mono (stores_ok (hs.of_keeps k₇ (by decide)) (o := offset 15) ⟨by decide, by rw [hsl]; omega_using [hc]⟩ _ _ _ _)
    fun t ht => ⟨?_, ?_, Scr.setFrame k₇ ht⟩
  · rw [ht, hsl]
    refine (fe_st4 _ _ (by decide) _ _ _ _).trans ?_
    show lo s₇ = _
    have hm : (s₆.gpr .x10).msb = decide (2 ^ 255 ≤ fe s.mem base oF) := by
      rw [w₆, BitVec.msb_eq_decide]
      apply decide_eq_decide.mpr
      have := (word s.mem base oF).isLt; have := (word s.mem base (oF + 8)).isLt
      have := (word s.mem base (oF + 16)).isLt; have := (word s.mem base (oF + 24)).isLt
      simp only [fe, val4]
      constructor <;> intro <;> omega_arith
    rw [v₇, hm, p₆]
    by_cases h : 2 ^ 255 ≤ fe s.mem base oF
    · simp only [h, decide_true, ↓reduceIte]
      omega_using [v₆]
    · simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]
  · rw [ht, ← k₇.mem, hsl]
    exact (st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide)

end VG.Proof.Ed25519.AArch64.Divstep

/-! # The theorem -/

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Divstep
open VG.Proof.Ed25519.AArch64 Word64
open VG.Proof.Mont.AArch64 (KeepRegs)
open VG.Proof.Divstep (MSt msteps divsteps)
open VG.Spec.X25519 (P)
open VG.Proof.X25519 (toFe)

variable {large : Bool}

private theorem P_val : (P : Int) = 2 ^ 255 - 19 := by simp [P]
private theorem P_odd : (P : Int) % 2 = 1 := by rw [P_val]; norm_num

/-- The divsteps' `(d, f, g)` after `k` batches from `x`. -/
def dsI (x k : Nat) : Int × Int × Int := divsteps (59 * k) (1, P, x)

/-- `2^590`. -/
def scale : Int := 2 ^ 590

/-- What the code holds after `k` batches from `x`. -/
structure BatchInv (x k : Nat) (base : Addr) (s : State) : Prop where
  i : s.gpr .x20 = half (dsI x k).1
  f : sv (fe s.mem base oF) = (dsI x k).2.1
  g : sv (fe s.mem base oG) = (dsI x k).2.2
  al : fe s.mem base oA < abMax
  bl : fe s.mem base oB < abMax
  ca : scale * (x * fe s.mem base oA : Int) ≡ 2 ^ (59 * k) * (dsI x k).2.1 [ZMOD P]
  cb : scale * (x * fe s.mem base oB : Int) ≡ 2 ^ (59 * k) * (dsI x k).2.2 [ZMOD P]
  z : x = 0 → (fe s.mem base oA : Int) ≡ 0 [ZMOD P]

private theorem dsI_le {x : Nat} (hx : x < P) (k : Nat) : |(dsI x k).2.1| ≤ P ∧ |(dsI x k).2.2| ≤ P :=
  Divstep.divsteps_le (by decide) P_odd (by rw [abs_of_nonneg (by positivity)]) (by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast hx.le) _

private theorem small {f : Int} (h : |f| ≤ P) : |f| < 2 ^ 255 := by rw [P_val] at h; omega_using [h]

/-- The low word of a number in two's complement. -/
theorem low_word {m : Mem} {base : Addr} {o : Nat} {f : Int} (h : sv (fe m base o) = f) :
    ((word m base o).toNat : Int) % 2 ^ 64 = f % 2 ^ 64 := by
  obtain ⟨b, hb⟩ := sv_split (fe m base o)
  rw [h] at hb
  simp only [fe, val4] at hb
  push_cast at hb
  generalize ((word m base o).toNat : Int) = a at *
  generalize ((word m base (o + 8)).toNat : Int) = c at *
  generalize ((word m base (o + 16)).toNat : Int) = d at *
  generalize ((word m base (o + 24)).toNat : Int) = e at *
  omega_using [hb]

theorem batchStart_ok {s : State} {base : Addr} (hs : Scr s base large) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block batchStart) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ t.gpr .x2 = word s.mem base oF ∧ t.gpr .x3 = word s.mem base oG ∧
      Keeps [.x19, .x2, .x3] s t := by
  have hc := workSize_ge large
  have e : batchStart = [Impl.Weierstrass.AArch64.decCounter] ++ ([ld .x2 oF] ++ [ld .x3 oG]) := rfl
  rw [e, WP.block_append_iff]
  refine WP.mono (Weierstrass.AArch64.decCounter_ok s hj hj' h19) fun s₁ ⟨c, q₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs.of_keeps q₁ (by decide)) (d := oF) (by decide) (by unfold oF; omega_using [hc]) .x2)
    fun s₂ ⟨v₂, q₂⟩ => ?_
  have k₂ : Keeps [.x19, .x2] s s₂ := (q₁.mono (by decide)).trans (q₂.mono (by decide))
  refine WP.mono (ld_ok (hs.of_keeps k₂ (by decide)) (d := oG) (by decide) (by unfold oG; omega_using [hc]) .x3)
    fun s₃ ⟨v₃, q₃⟩ => ⟨?_, ?_, ?_, (k₂.mono (by decide)).trans (q₃.mono (by decide))⟩
  · rw [q₃.gpr _ (by decide), q₂.gpr _ (by decide), c]
  · rw [q₃.gpr _ (by decide), v₂, q₁.mem]
  · rw [v₃, k₂.mem]

/-- The congruence of a row of `a` and `b`. -/
private theorem row_cong {x A B : Nat} {u v f g f' c R m k : Int}
    (ca : k * (x * A : Int) ≡ c * f [ZMOD P]) (cb : k * (x * B : Int) ≡ c * g [ZMOD P])
    (hR : R = u * A + v * B + (2 ^ 255 - 19) * m) (hf : 2 ^ 59 * f' = u * f + v * g) :
    k * (x * R) ≡ c * 2 ^ 59 * f' [ZMOD P] := by
  have h := (ca.mul_left u).add (cb.mul_left v)
  have e1 : c * 2 ^ 59 * f' = u * (c * f) + v * (c * g) := by rw [mul_assoc, hf]; ring
  rw [e1]
  refine Int.ModEq.trans ?_ h
  rw [hR, ← P_val, Int.modEq_iff_dvd]
  exact ⟨-(k * x * m), by ring⟩

theorem batch_ok {x k : Nat} (hx : x < P) (hk : k < 10) {s : State} {base : Addr} (hs : Scr s base large)
    (hI : BatchInv x k base s) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block batch) s fun t =>
      BatchInv x (k + 1) base t ∧ t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ Outside base 192 512 s.mem t.mem ∧
      KeepRegs invRegs s t := by
  obtain ⟨hi, hf, hg, al, bl, ca, cb, hz⟩ := hI
  have hs1 : dsI x (k + 1) = divsteps 59 (dsI x k) := by
    unfold dsI; rw [show 59 * (k + 1) = 59 * k + 59 by ring, Divstep.divsteps_add]
  obtain ⟨hod, hof⟩ : (dsI x k).1 % 2 = 1 ∧ (dsI x k).2.1 % 2 = 1 := Divstep.divsteps_odd (by decide) P_odd _
  obtain ⟨lf, lg⟩ := dsI_le hx (k + 1)
  have hd : |(dsI x k).1| ≤ 2 ^ 30 := by
    have h := Divstep.divsteps_d (1, (P : Int), (x : Int)) (59 * k)
    simp only [abs_one] at h
    have : (59 * k : Int) ≤ 59 * 9 := by exact_mod_cast (by omega_using [hk] : 59 * k ≤ 59 * 9)
    push_cast at h
    have h : |(dsI x k).1| ≤ 1 + 2 * (59 * k) := h
    linarith
  have hzero : x = 0 → (dsI x k).2.2 = 0 := fun hx0 => by
    unfold dsI; rw [hx0]; exact (Divstep.divsteps_zero (t := (1, (P : Int), ((0 : Nat) : Int))) (by simp) _).1
  rw [hs1] at lf lg
  generalize dsI x k = st at hi hf hg ca cb hs1 hod hof lf lg hd hzero
  obtain ⟨d, f, g⟩ := st
  simp only at hi hf hg ca cb hod hof hd hzero
  obtain ⟨m1, m2⟩ := Divstep.msteps_mat (d := d) (g := g) hof 59
  obtain ⟨b1, b2⟩ := Divstep.msteps_bnd d f g 59
  have hdfg := Divstep.msteps_dfg 59 (MSt.init d f g)
  have hg0 : g = 0 → (msteps 59 (MSt.init d f g)).v = 0 := fun hg => by
    subst hg; rw [MSt.init, Divstep.msteps_g0]; simp
  simp only [MSt.init] at hdfg
  rw [← hdfg] at hs1 lf lg
  simp only at lf lg
  simp only [batch, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (batchStart_ok hs hj hj' h19) fun s₁ ⟨c₁, f₁, g₁, q₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (words_ok s₁ (d := d) (f := f) (g := g) hd hod hof (by rw [q₁.gpr _ (by decide)]; exact hi)
    (by rw [f₁]; exact low_word hf) (by rw [g₁]; exact low_word hg)) fun s₂ ⟨i₂, M₂, q₂⟩ => ?_
  simp only [MSt.init] at i₂ M₂ m1 m2 b1 b2 hg0
  generalize msteps 59 ⟨d, f, g, 1, 0, 0, 1⟩ = T at *
  have k₂ : Keeps invRegs s s₂ := (q₁.mono (by decide)).trans (q₂.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (bias_ok s₂ M₂.u M₂.v M₂.q M₂.r (le_trans (le_add_of_nonneg_right (abs_nonneg _)) b1)
    (le_trans (le_add_of_nonneg_left (abs_nonneg _)) b1) (le_trans (le_add_of_nonneg_right (abs_nonneg _)) b2)
    (le_trans (le_add_of_nonneg_left (abs_nonneg _)) b2)) fun s₃ ⟨u₃, v₃, q₃, r₃, z₃, kp₃⟩ => ?_
  have k₃ : Keeps invRegs s s₃ := k₂.trans (kp₃.mono (by decide))
  have hs₃ := hs.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (updateFG_ok hs₃ z₃ u₃ v₃ q₃ r₃ (f' := T.f) (g' := T.g) (by rw [k₃.mem, hf, hg]; exact m1)
    (by rw [k₃.mem, hf, hg]; exact m2) (small lf) (small lg)) fun s₄ ⟨f₄, g₄, o₄, k₄⟩ => ?_
  have hs₄ := Scr.of_keepRegs' hs₃ k₄ (by decide)
  have W₄ : ∀ o, o = oA ∨ o = oB → fe s₄.mem base o = fe s.mem base o := by
    intro o ho
    have w : ∀ d, 256 ≤ d ∧ d + 8 ≤ 320 → word s₄.mem base d = word s.mem base d := fun d hd => by
      rw [← k₃.mem]
      refine (Mem.readW_congr fun i hi => (o₄ _ ?_).symm).symm
      rw [ofs_off base (by omega_using [hd, hi])]
      omega_using [hd, hi]
    rcases ho with rfl | rfl <;> simp only [fe] <;>
      rw [w _ (by decide), w _ (by decide), w _ (by decide), w _ (by decide)]
  have A₄ := W₄ oA (Or.inl rfl)
  have B₄ := W₄ oB (Or.inr rfl)
  refine WP.mono (updateAB_ok hs₄ (by rw [k₄.gpr _ (by decide), z₃]) (by rw [k₄.gpr _ (by decide)]; exact u₃)
    (by rw [k₄.gpr _ (by decide)]; exact v₃) (by rw [k₄.gpr _ (by decide)]; exact q₃)
    (by rw [k₄.gpr _ (by decide)]; exact r₃) b1 b2 (by rw [A₄]; exact al) (by rw [B₄]; exact bl))
    fun t ⟨l₅, l₅', ⟨ma, a₅⟩, ⟨mb, b₅⟩, o₅, k₅⟩ => ?_
  rw [A₄, B₄] at a₅ b₅
  have kt : KeepRegs invRegs s t := (⟨k₃.gpr, k₃.rd, k₃.wr, k₃.sp⟩ : KeepRegs invRegs s s₃).trans
    ((k₄.trans k₅).mono (by decide))
  have F₅ : fe t.mem base oF = fe s₄.mem base oF := o₅.fe (by decide) (by decide)
  have G₅ : fe t.mem base oG = fe s₄.mem base oG := o₅.fe (by decide) (by decide)
  have hP : (2 : Int) ^ (59 * (k + 1)) = 2 ^ (59 * k) * 2 ^ 59 := by rw [← pow_add]; ring_nf
  refine ⟨⟨?_, ?_, ?_, l₅, l₅', ?_, ?_, fun hx0 => ?_⟩, ?_, ?_, kt⟩
  · rw [hs1, k₅.gpr _ (by decide), k₄.gpr _ (by decide), kp₃.gpr _ (by decide), i₂]
  · rw [hs1, F₅, f₄]
  · rw [hs1, G₅, g₄]
  · rw [hs1, hP]; exact row_cong ca cb a₅ m1
  · rw [hs1, hP]; exact row_cong ca cb b₅ m2
  · rw [a₅, hg0 (hzero hx0), ← P_val, Int.modEq_iff_dvd]
    obtain ⟨n, hn⟩ := Int.modEq_iff_dvd.mp (hz hx0)
    exact ⟨T.u * n - ma, by linear_combination T.u * hn⟩
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), kp₃.gpr _ (by decide), q₂.gpr _ (by decide), c₁]
  · intro y hy
    rw [o₅ y (by omega_using [hy]), o₄ y (by omega_using [hy]), k₃.mem]

/-! ## The result -/

private theorem b0_spec : scale * b0 ≡ 1 [ZMOD P] := by unfold Int.ModEq scale b0; decide +kernel

private theorem toZ_toFe (n : Nat) : Ed25519.toZ (toFe n) = (n : ZMod P) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast]
  rfl

/-- The result's residue, from the last invariant. -/
private theorem result {x A F R : Nat} (hx : x < P) (hA : A < abMax) (hF : F < 2 ^ 256) (hf : sv F = (dsI x 10).2.1)
    (ca : scale * (x * A : Int) ≡ 2 ^ (59 * 10) * (dsI x 10).2.1 [ZMOD P]) (hz : x = 0 → (A : Int) ≡ 0 [ZMOD P])
    (hR : R = if 2 ^ 255 ≤ F then 2 ^ 256 - 38 - A else A) : (R : ZMod P) = (x : ZMod P) ^ (P - 2) := by
  have twoP : ((2 ^ 256 - 38 : Nat) : ZMod P) = 0 := by
    rw [show (2 ^ 256 - 38 : Nat) = P * 2 by simp [P], Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have neg : ((2 ^ 256 - 38 - A : Nat) : ZMod P) = -(A : ZMod P) := by
    rw [Nat.cast_sub (by unfold abMax at hA; omega_using [hA]), twoP, zero_sub]
  by_cases h0 : x = 0
  · have ha := (ZMod.intCast_eq_intCast_iff _ _ _).2 (hz h0)
    push_cast at ha
    rw [hR, h0, Nat.cast_zero, zero_pow (by simp [P])]
    split
    · rw [neg, ha, neg_zero]
    · exact ha
  · have hdone := Divstep.divsteps_590 (f := (P : Int)) (g := (x : Int)) P_odd (by positivity)
      (by exact_mod_cast hx.le) (by rw [P_val]; norm_num) (n := 590) le_rfl
    have hcop : Int.gcd (P : Int) (x : Int) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_of_lt_prime h0 hx Ed25519.prime_field
    have hs : dsI x 10 = divsteps 590 (1, (P : Int), (x : Int)) := rfl
    rw [hs] at hf ca
    generalize (divsteps 590 (1, (P : Int), (x : Int))).2.1 = f at hdone hf ca
    rw [hcop] at hdone
    have hf1 : f = 1 ∨ f = -1 := by omega_using [hdone]
    have hc := Divstep.cancel_pow2 (N := 59 * 10) P_odd (by rw [P_val]; norm_num) ca
    have hc := (ZMod.intCast_eq_intCast_iff _ _ _).2 hc
    push_cast at hc
    have hxR : (x : ZMod P) * (R : ZMod P) = 1 := by
      unfold sv at hf
      rcases hf1 with rfl | rfl
      · have : ¬ 2 ^ 255 ≤ F := fun h => by
          rw [ite_eq_right (by omega_using [h])] at hf
          omega_using [hf, hF]
        rw [hR, ite_eq_right this, hc, Int.cast_one]
      · have : 2 ^ 255 ≤ F := by
          by_contra h
          rw [ite_eq_left (by omega_using [h])] at hf
          omega_using [hf]
        rw [hR, ite_eq_left this, neg, mul_neg, hc, Int.cast_neg, Int.cast_one, neg_neg]
    have hX : (x : ZMod P) ≠ 0 := fun h => by rw [h, zero_mul] at hxR; exact zero_ne_one hxR
    calc (R : ZMod P) = (R : ZMod P) * x * (x : ZMod P) ^ (P - 2) := (Ed25519.mul_pow_inv hX _).symm
      _ = x * R * (x : ZMod P) ^ (P - 2) := by ring
      _ = (x : ZMod P) ^ (P - 2) := by rw [hxR, one_mul]

theorem invert_sound {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa VG.Impl.Ed25519.AArch64.Divstep.invert s fun t =>
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) ∧
      Outside base 192 512 s.mem t.mem ∧ KeepRegs invRegs s t := by
  unfold invert
  refine WP.seq (WP.mono (start_ok hs) fun a ⟨fa, aa, ba, ga, ia, ca, oa, ka⟩ => ?_)
  have hsa := Scr.of_keepRegs' hs ka (by decide)
  obtain ⟨x, hxe⟩ : ∃ x, x = fe s.mem base 128 % P := ⟨_, rfl⟩
  have hx : x < P := by rw [hxe]; exact Nat.mod_lt _ (by decide)
  rw [← hxe] at ga
  have hP : P = 2 ^ 255 - 19 := rfl
  have I0 : BatchInv x 0 base a := by
    have e : dsI x 0 = (1, (P : Int), (x : Int)) := rfl
    refine ⟨by rw [ia, e]; show (0 : BitVec 64) = half 1; decide, ?_, ?_, by rw [aa]; decide, by rw [ba]; decide, ?_, ?_, fun _ => by rw [aa]; rfl⟩
    · rw [fa, e]; show sv P = (P : Int); decide
    · rw [ga, e]; unfold sv; rw [ite_eq_left (by rw [hP] at hx; omega_using [hx])]
    · rw [aa, e]
      simp only [Nat.cast_zero, mul_zero, pow_zero, one_mul]
      exact (Int.emod_self.trans (by simp)).symm
    · rw [ba, e]
      simp only [mul_zero, pow_zero, one_mul]
      have h' := b0_spec.mul_left (x : Int)
      rw [mul_one] at h'
      rw [show scale * (x * b0) = x * (scale * b0) by ring]
      exact h'
  refine WP.seq (Weierstrass.AArch64.countLoop_ok (n := 10) (by decide)
    (Inv := fun j t => BatchInv x (10 - j) base t ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧ Scr t base large ∧
      Outside base 192 512 a.mem t.mem ∧ KeepRegs invRegs a t)
    (fun j t h1 h10 ⟨It, ct, st, ot, kt⟩ => ?_)
    (fun t ⟨It, _, st, ot, kt⟩ => ?_) (by decide) ⟨I0, ca, hsa, Outside.refl _ _ _ _, fun _ _ => rfl, rfl, rfl, rfl⟩)
  · refine WP.mono (batch_ok hx (k := 10 - j) (by omega_using [h1]) st It h1 (by omega_using [h10]) ct)
      fun u ⟨Iu, cu, ou, ku⟩ => ⟨⟨?_, cu, Scr.of_keepRegs' st ku (by decide), ot.trans ou, kt.trans ku⟩, cu⟩
    rw [show 10 - (j - 1) = 10 - j + 1 by omega_using [h1, h10]]
    exact Iu
  · refine WP.mono (finish_ok st It.al) fun u ⟨vu, ou, ku⟩ => ⟨?_, (oa.trans ot).trans ou, (ka.trans kt).trans ku⟩
    rw [Nat.sub_zero] at It
    have hr := result hx It.al (val4_lt _ _ _ _) It.f It.ca It.z vu
    rw [X25519.invert_eq, ← Ed25519.toZ_inj, Ed25519.toZ_pow]
    show Ed25519.toZ (toFe (fe u.mem base 544)) = Ed25519.toZ (toFe (fe s.mem base 128)) ^ (P - 2)
    rw [toZ_toFe, toZ_toFe, hr, hxe, ZMod.natCast_mod]

instance sound : Sound where
  invert_ok hs := WP.mono (invert_sound hs) fun t ⟨v, o, k⟩ =>
    ⟨v, k.mono (by decide), k.gpr _ (by decide), o⟩

end VG.Proof.Ed25519.AArch64.Divstep
