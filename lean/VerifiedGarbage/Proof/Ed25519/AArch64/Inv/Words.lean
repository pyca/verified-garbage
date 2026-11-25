module

public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvPacked
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.WordBasic
public import VerifiedGarbage.Proof.Divstep.PackedDef
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring

/-!
# Ed25519 and X25519 on AArch64: a batch's packed divsteps

A step's block is `mstep`'s on the rows (`step_ok`), with `i = (d - 1) / 2` in
`x20`, a chunk's block its steps from the batch's state so far (`Chunk`), and
the batch's four chunks leave `i` and the matrix of 59 steps (`words_ok`).
-/

@[expose] public section

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
