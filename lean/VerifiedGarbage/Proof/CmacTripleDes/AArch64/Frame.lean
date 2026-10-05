import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.CmacTripleDes.AArch64.Round
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Linear
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Impl.CmacTripleDes.AArch64
import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit`. -/
section

/-!
# The DES block's AArch64 code as literals, for kernel-evaluated checks

The tables, the groups of `P`, `IP`, `IP⁻¹` and the block are each evaluated
once, here: the checks of each part (`Layout.lean`, `Round.lean`,
`Block.lean`) and the literals of the functions that run the block
(`Lit.lean`) read these literals rather than evaluate the S-boxes and bit
permutations again.
-/

namespace VG

materialize_table Impl.CmacTripleDes.AArch64.sTable 256
materialize_value Impl.CmacTripleDes.AArch64.pGroups
materialize_value Impl.CmacTripleDes.AArch64.ipCode
materialize_value Impl.CmacTripleDes.AArch64.fpCode
materialize_value Impl.CmacTripleDes.AArch64.spreadPre
materialize_code Impl.CmacTripleDes.AArch64.block

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Layout`. -/
section

/-!
# DES on AArch64: the spread words and the tables

`spreadW w` is `w` rotated left by `rot` bits and spread (`xSrc`), and
`spread k` a round key spread. These are the facts about the layout that the
round needs, each checked over the finite index maps: byte `l` of the
S-boxes' index, `spread k ⊕ spreadW r`, is the input of box `boxOf l`, with
its table in the top two bits (`index_byte`); and the tables hold the
S-boxes' outputs at `posOf` (`sTable_bit`).
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes

/-- `w` rotated left by `rot` bits and spread. -/
def spreadW (w : BitVec 32) : BitVec 64 :=
  ofBits 64 fun p => xBit p && w.getLsbD ((xSrc p + 32 - rot) % 32)

theorem getLsbD_spreadW (w : BitVec 32) {p : Nat} (hp : p < 64) :
    (VG.Proof.CmacTripleDes.AArch64.spreadW w).getLsbD p = (xBit p && w.getLsbD ((xSrc p + 32 - rot) % 32)) := by
  rw [VG.Proof.CmacTripleDes.AArch64.spreadW, getLsbD_ofBits, decide_eq_true hp, Bool.true_and]

/-- The box whose input byte `l` holds. -/
def boxOf (l : Nat) : Nat := [2, 0, 6, 4, 1, 7, 5, 3].getD l 0

theorem boxOf_laneOf : ∀ i < 8, VG.Proof.CmacTripleDes.AArch64.boxOf (laneOf i) = i := by decide
theorem laneOf_boxOf : ∀ l < 8, laneOf (VG.Proof.CmacTripleDes.AArch64.boxOf l) = l := by decide
theorem laneOf_lt : ∀ i < 8, laneOf i < 8 := by decide
theorem boxOf_lt : ∀ l < 8, VG.Proof.CmacTripleDes.AArch64.boxOf l < 8 := by decide
theorem tableOf_lt : ∀ i < 8, boxTable i < 4 := by decide

/-- Byte `l` of a spread word: the expansion's bits for box `boxOf l`, and
two zero bits. -/
theorem chunk_layout : ∀ l < 8, ∀ t < 8,
    xBit (8 * l + t) = decide (t < 6) ∧
      (t < 6 → (xSrc (8 * l + t) + 32 - rot) % 32 = expSrc (6 * (7 - VG.Proof.CmacTripleDes.AArch64.boxOf l) + t)) := by
  decide

/-! ## The round keys -/

/-- The round key `k` spread: in byte `laneOf i`, box `i`'s six bits of `k`,
and `boxTable i` in the top two bits (`offsets`). -/
def spread (k : BitVec 64) : BitVec 64 :=
  ofBits 64 fun p =>
    if p % 8 < 6 then k.getLsbD (6 * (7 - VG.Proof.CmacTripleDes.AArch64.boxOf (p / 8)) + p % 8) else offsets.getLsbD p

theorem offsets_bits : ∀ l < 8, ∀ t < 8,
    offsets.getLsbD (8 * l + t) = (decide (6 ≤ t) && (boxTable (VG.Proof.CmacTripleDes.AArch64.boxOf l)).testBit (t - 6)) := by
  decide

theorem getLsbD_spread (k : BitVec 64) {l t : Nat} (hl : l < 8) (ht : t < 8) :
    (VG.Proof.CmacTripleDes.AArch64.spread k).getLsbD (8 * l + t) =
      if t < 6 then k.getLsbD (6 * (7 - VG.Proof.CmacTripleDes.AArch64.boxOf l) + t)
      else (boxTable (VG.Proof.CmacTripleDes.AArch64.boxOf l)).testBit (t - 6) := by
  rw [VG.Proof.CmacTripleDes.AArch64.spread, getLsbD_ofBits, decide_eq_true (by omega), Bool.true_and,
    show (8 * l + t) % 8 = t by omega, show (8 * l + t) / 8 = l by omega]
  split
  · rfl
  · rw [VG.Proof.CmacTripleDes.AArch64.offsets_bits l hl t ht, decide_eq_true (by omega), Bool.true_and]

/-- Byte `l` of the S-boxes' index: box `boxOf l`'s input, after its table. -/
theorem index_byte (k : BitVec 64) (r : BitVec 32) {l : Nat} (hl : l < 8) :
    (VG.Proof.CmacTripleDes.AArch64.spread k ^^^ VG.Proof.CmacTripleDes.AArch64.spreadW r).extractLsb' (8 * l) 8 =
      BitVec.ofNat 8 (2 ^ 6 * boxTable (VG.Proof.CmacTripleDes.AArch64.boxOf l) + (chunk r (k.setWidth 48) (VG.Proof.CmacTripleDes.AArch64.boxOf l)).toNat) := by
  have hb := VG.Proof.CmacTripleDes.AArch64.boxOf_lt l hl
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [BitVec.getLsbD_extractLsb', decide_eq_true ht, Bool.true_and, BitVec.getLsbD_xor,
    VG.Proof.CmacTripleDes.AArch64.getLsbD_spread k hl ht, VG.Proof.CmacTripleDes.AArch64.getLsbD_spreadW r (by omega), BitVec.getLsbD_ofNat,
    decide_eq_true ht, Bool.true_and,
    Nat.testBit_two_pow_mul_add _ (chunk r (k.setWidth 48) (VG.Proof.CmacTripleDes.AArch64.boxOf l)).isLt]
  obtain ⟨hx, he⟩ := VG.Proof.CmacTripleDes.AArch64.chunk_layout l hl t ht
  rw [hx]
  by_cases h6 : t < 6
  · rw [ite_eq_left h6, ite_eq_left h6, he h6, BitVec.testBit_toNat, getLsbD_chunk _ _ hb h6,
      BitVec.getLsbD_setWidth, decide_eq_true (show 6 * (7 - VG.Proof.CmacTripleDes.AArch64.boxOf l) + t < 48 by omega),
      Bool.true_and, decide_eq_true h6, Bool.true_and, Bool.xor_comm]
  · rw [ite_eq_right h6, ite_eq_right h6, decide_eq_false h6, Bool.false_and, Bool.xor_false]

/-! ## The tables -/

theorem sTable_bit : ∀ i < 8, ∀ x < 64, ∀ q < 4,
    (sTable (2 ^ 6 * boxTable i + x)).getLsbD (posOf i q) =
      (Spec.TripleDes.sBox i (BitVec.ofNat 6 x)).getLsbD q := by
  lit_decide

/-! ## `P` -/

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide


/-- Bit `p` of the spread `P(S)` is output bit `u % 4` of box `7 − u / 4`,
at its bit of `y`, where `u = pSrc ((xSrc p + 32 − rot) % 32)`. -/
theorem ySrc_eq {p : Nat} (hp : xBit p = true) :
    ySrc p = some (8 * laneOf (7 - pSrc ((xSrc p + 32 - rot) % 32) / 4) +
      posOf (7 - pSrc ((xSrc p + 32 - rot) % 32) / 4) (pSrc ((xSrc p + 32 - rot) % 32) % 4)) := by
  simp [ySrc, hp]

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Round`. -/
section

/-!
# A DES round on AArch64

The round's three parts: the S-boxes' index, the spread round key at `x10`
XORed with `R` (`sIn_ok`), in `v0` and its quarters in `v1`–`v3`; the
S-boxes' outputs by `tbl` (`sOut_ok`, from `select_full_run`); and `L`
XORed with groups of them (`pOut_ok`), checked by evaluation over the lane
domain (`Straight.check`). `round_ok` composes them: the spread
`L ⊕ f(R, K)`.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Straight VG.AArch64.Tbl VG.Bitslice
  VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64 VG.Impl.Tbl.AArch64 VG.Proof.CmacTripleDes

/-- What the rounds keep in the vector registers: the tables, and 64, 128
and 192 in every byte of `v4`, `v5` and `v6`. -/
structure Consts (s : VG.AArch64.State) : Prop where
  tab : ∀ k < 256, tbyte s.v k = sTable k
  c64 : s.v .v4 = bc 64
  c128 : s.v .v5 = bc 128
  c192 : s.v .v6 = bc 192

theorem Consts.congr {s s' : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.Consts s)
    (hv : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s'.v w = s.v w) : VG.Proof.CmacTripleDes.AArch64.Consts s' where
  tab k hk := by rw [tbyte_congr (fun r a b c d _ _ => hv r a b c d) k hk]; exact h.tab k hk
  c64 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c64
  c128 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c128
  c192 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c192

/-! ## The index -/

/-- The step of the key pointer. -/
def kstep (down : Bool) : Instr := if down then .subImm .x .x10 .x10 8 else .addImm .x .x10 .x10 8

theorem exec_kstep (s : VG.AArch64.State) (down : Bool) :
    exec (VG.Proof.CmacTripleDes.AArch64.kstep down) s =
      some (s.write .x .x10 (if down then s.gpr .x10 - 8 else s.gpr .x10 + 8)) := by
  cases down
  · simp only [VG.Proof.CmacTripleDes.AArch64.kstep, Bool.false_eq_true, ite_false, exec_addImm_x (by decide : 8 < 4096),
      State.read, BitVec.setWidth_eq]; rfl
  · simp only [VG.Proof.CmacTripleDes.AArch64.kstep, ite_true, exec_subImm_x (by decide : 8 < 4096), State.read,
      BitVec.setWidth_eq]; rfl

theorem sIn_eq (b : Reg) (down : Bool) : sIn b down =
    [.ldr .x .x5 .x10 0, VG.Proof.CmacTripleDes.AArch64.kstep down, .logic .eor .x .x5 .x5 b, .vop (.ins .d2 .v0 0 .x5),
     .vop (.logic .eor .v1 .v0 .v4), .vop (.logic .eor .v2 .v0 .v5),
     .vop (.logic .eor .v3 .v0 .v6)] := rfl

theorem vbyte_setLane0 (x : BitVec 128) (y : BitVec 64) {e : Nat} (he : e < 8) :
    vbyte (setLane x 64 0 y) e = y.extractLsb' (8 * e) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, setLane, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, Nat.mul_zero, Nat.sub_zero,
    show 8 * e + i < 128 by omega, show 8 * e + i < 64 by omega, show ¬ 8 * e + i < 0 by omega]
  simp

theorem sIn_ok (s : VG.AArch64.State) {b : Reg} (hb5 : b ≠ .x5) (hb10 : b ≠ .x10) (down : Bool)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x10) 8) (hc : VG.Proof.CmacTripleDes.AArch64.Consts s) :
    ∃ s', runBlock isa (sIn b down) s = some s' ∧
      (∀ e < 8, vbyte (s'.v .v0) e =
        (s.mem.readW (s.gpr .x10) 64 ^^^ s.gpr b).extractLsb' (8 * e) 8) ∧
      (∀ e < 16, vbyte (s'.v .v1) e = vbyte (s'.v .v0) e ^^^ 64) ∧
      (∀ e < 16, vbyte (s'.v .v2) e = vbyte (s'.v .v0) e ^^^ 128) ∧
      (∀ e < 16, vbyte (s'.v .v3) e = vbyte (s'.v .v0) e ^^^ 192) ∧
      s'.gpr .x10 = (if down then s.gpr .x10 - 8 else s.gpr .x10 + 8) ∧
      (∀ r, r ≠ .x5 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s'.v w = s.v w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hk' : InRegions (s.rd ++ s.wr) (s.gpr .x10 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero]; exact hk
  let K := s.mem.readW (s.gpr .x10 + BitVec.ofNat 64 0) 64
  let s₁ := s.write .x .x5 K
  let s₂ := s₁.write .x .x10 (if down then s₁.gpr .x10 - 8 else s₁.gpr .x10 + 8)
  let s₃ := s₂.write .x .x5 (s₂.read .x .x5 ^^^ s₂.read .x b)
  let s₄ := s₃.setV .v0 (setLane (s₃.v .v0) 64 0 (s₃.gpr .x5))
  let s₅ := s₄.setV .v1 (s₄.v .v0 ^^^ s₄.v .v4)
  let s₆ := s₅.setV .v2 (s₅.v .v0 ^^^ s₅.v .v5)
  let s₇ := s₆.setV .v3 (s₆.v .v0 ^^^ s₆.v .v6)
  have x5₃ : s₃.gpr .x5 = K ^^^ s.gpr b := by
    simp only [s₃, s₂, s₁, State.read, gpr_write_self, BitVec.setWidth_eq,
      gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x10), gpr_write_of_ne _ _ _ hb10,
      gpr_write_of_ne _ _ _ hb5]
  have v0₇ : s₇.v .v0 = setLane (s.v .v0) 64 0 (K ^^^ s.gpr b) := by
    simp only [s₇, s₆, s₅, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
      v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1)]
    rw [show s₄.v .v0 = setLane (s₃.v .v0) 64 0 (s₃.gpr .x5) from v_setV_self _ _ _, x5₃]; rfl
  have vs : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s₇.v w = s.v w := by
    intro w h0 h1 h2 h3
    simp only [s₇, s₆, s₅, s₄, v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h1,
      v_setV_of_ne _ _ h0]; rfl
  have c₄ : ∀ w, w = .v4 ∨ w = .v5 ∨ w = .v6 → s₆.v w = s.v w := by
    intro w hw
    rcases hw with rfl | rfl | rfl <;>
      simp only [s₆, s₅, s₄, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v2),
        v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v2),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v1), v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v1),
        v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v1), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v0),
        v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v0), v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v0)] <;> rfl
  have z₆ : s₆.v .v0 = s₇.v .v0 := (v_setV_of_ne _ _ (by decide)).symm
  have z₅ : s₅.v .v0 = s₇.v .v0 := by
    rw [← z₆]; exact (v_setV_of_ne _ _ (by decide)).symm
  have z₄ : s₄.v .v0 = s₇.v .v0 := by
    rw [← z₅]; exact (v_setV_of_ne _ _ (by decide)).symm
  refine ⟨s₇, ?_, fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_,
    fun r h5 h10 => ?_, vs, rfl, rfl, rfl, rfl⟩
  · rw [VG.Proof.CmacTripleDes.AArch64.sIn_eq, runBlock_cons, exec_ldr_x (by decide) hk', runStep_some, runBlock_cons,
      VG.Proof.CmacTripleDes.AArch64.exec_kstep, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons,
      exec_insd _ _ _ (by decide), runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, exec_eorv, runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_nil]
  · rw [v0₇, VG.Proof.CmacTripleDes.AArch64.vbyte_setLane0 _ _ he]
    simp only [K, BitVec.add_zero]
  · have : s₇.v .v1 = s₄.v .v0 ^^^ s₄.v .v4 := by
      simp only [s₇, s₆, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v2)]; exact v_setV_self _ _ _
    rw [this, vbyte_xor, z₄, show s₄.v .v4 = s.v .v4 from by
      rw [← c₄ .v4 (by simp)]; simp only [s₆, s₅, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v2),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v1)], hc.c64, vbyte_bc _ he]
  · have : s₇.v .v2 = s₅.v .v0 ^^^ s₅.v .v5 := by
      simp only [s₇, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3)]; exact v_setV_self _ _ _
    rw [this, vbyte_xor, z₅, show s₅.v .v5 = s.v .v5 from by
      rw [← c₄ .v5 (by simp)]; simp only [s₆, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v2)],
      hc.c128, vbyte_bc _ he]
  · have : s₇.v .v3 = s₆.v .v0 ^^^ s₆.v .v6 := v_setV_self _ _ _
    rw [this, vbyte_xor, z₆, c₄ .v6 (by simp), hc.c192, vbyte_bc _ he]
  · simp only [s₇, s₆, s₅, s₄, gpr_setV, s₃, gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x5),
      s₂, gpr_write_self, BitVec.setWidth_eq, s₁]
  · simp only [s₇, s₆, s₅, s₄, gpr_setV, s₃, s₂, s₁, gpr_write_of_ne _ _ _ h5,
      gpr_write_of_ne _ _ _ h10]

/-! ## The S-boxes -/

theorem exec_umovx0 (s : VG.AArch64.State) (d : Reg) (n : VReg) :
    exec (.umov .x d n 0) s = some (s.write .x d ((s.v n).extractLsb' 0 64)) := by
  simp [exec, Size.bits]

theorem extract_vbyte (v : BitVec 128) {l : Nat} (hl : l < 8) :
    ((v.extractLsb' 0 64).extractLsb' (8 * l) 8) = vbyte v l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [vbyte, hi, show 8 * l + i < 64 by omega]

/-- The S-boxes' outputs `y`, in `x5`: byte `l` is the table's byte at the
index's byte `l`. -/
theorem sOut_ok {s : VG.AArch64.State} (I : Nat → BitVec 8)
    (h0 : ∀ e < 16, vbyte (s.v .v0) e = I e)
    (h1 : ∀ e < 16, vbyte (s.v .v1) e = I e ^^^ 64)
    (h2 : ∀ e < 16, vbyte (s.v .v2) e = I e ^^^ 128)
    (h3 : ∀ e < 16, vbyte (s.v .v3) e = I e ^^^ 192) :
    ∃ s', runBlock isa sOut s = some s' ∧
      (∀ l < 8, (s'.gpr .x5).extractLsb' (8 * l) 8 = tbyte s.v (I l).toNat) ∧
      (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s'.v w = s.v w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨d, rund, d0, dv⟩ := select_full_run I h0 h1 h2 h3
  let t := d.write .x .x5 ((d.v .v0).extractLsb' 0 64)
  refine ⟨t, ?_, fun l hl => ?_, fun r hr => ?_, fun w a b c e => ?_, ?_, ?_, ?_, ?_⟩
  · rw [sOut, runBlock_cat_some rund (by rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_umovx0, runStep_some, runBlock_nil])]
  · simp only [t, gpr_write_self, BitVec.setWidth_eq]
    rw [VG.Proof.CmacTripleDes.AArch64.extract_vbyte _ hl, d0 l (by omega)]
  · simp only [t, gpr_write_of_ne _ _ _ hr, dv.gpr]
  · simp only [t, v_write]; exact dv.2 w (by simp [a, b, c, e])
  · simp only [t, mem_write, dv.mem]
  · simp only [t, rd_write, dv.rd]
  · simp only [t, wr_write, dv.wr]
  · simp only [t, sp_write]; rw [dv.1]

/-! ## `P` -/

/-- No memory. -/
def oCfg : Cfg := { base := .x15, slots := 0, ext := .x14, exts := 0 }

theorem oCfg_ok (s : VG.AArch64.State) : Ok VG.Proof.CmacTripleDes.AArch64.oCfg s :=
  ⟨fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.AArch64.oCfg]), fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.AArch64.oCfg]), by decide,
    fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.AArch64.oCfg])⟩

theorem frame_oCfg {s : VG.AArch64.State} {m m' : Mem} (h : Frame [slotRegion VG.Proof.CmacTripleDes.AArch64.oCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, VG.Proof.CmacTripleDes.AArch64.oCfg, Region.Contains]

/-- The masks and their registers. -/
def maskConsts : List (Reg × BitVec 64) :=
  pGroups.zipIdx.map fun (g, k) => (maskReg k, BitVec.ofNat 64 g.2)

/-- The mask registers hold the masks. -/
def Masks (s : VG.AArch64.State) : Prop := ∀ r v, (r, v) ∈ VG.Proof.CmacTripleDes.AArch64.maskConsts → s.gpr r = v

/-- The mask registers are none of the round's others. -/
theorem maskRegs_ne : ∀ p ∈ VG.Proof.CmacTripleDes.AArch64.maskConsts, p.1 ≠ .x5 ∧ p.1 ≠ .x10 ∧ p.1 ≠ .x11 ∧ p.1 ≠ .x12 ∧
    p.1 ≠ .x16 ∧ p.1 ≠ .x6 ∧ p.1 ≠ .x7 ∧ p.1 ≠ .x14 ∧ p.1 ≠ .x15 ∧ p.1 ≠ .x1 ∧ p.1 ≠ .x2 ∧
    p.1 ≠ .x3 ∧ p.1 ≠ .x4 := by
  lit_decide

theorem Masks.congr {s s' : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.Masks s) (hg : ∀ p ∈ VG.Proof.CmacTripleDes.AArch64.maskConsts, s'.gpr p.1 = s.gpr p.1) :
    VG.Proof.CmacTripleDes.AArch64.Masks s' := fun r v hp => by rw [hg (r, v) hp]; exact h r v hp

theorem ySrc_bound : ∀ p < 64, (ySrc p).all (· < 64) = true := by lit_decide

theorem ySrc_lt {p q : Nat} (hp : p < 64) (h : ySrc p = some q) : q < 64 := by
  have := VG.Proof.CmacTripleDes.AArch64.ySrc_bound p hp
  rw [h] at this
  simpa using this

/-- The inputs of `pOut a`: `y` (input word 0) and `a` (input word 1). -/
def pIns (a : Reg) : List (Reg × Nat) := [(.x5, 0), (a, 1)]

/-- Bit `p` of `a` afterwards: bit `ySrc p` of `y` XORed in, where it is spread. -/
def pG (p : Nat) : List Nat :=
  match ySrc p with
  | some q => [q, 64 + p]
  | none => [64 + p]

theorem pOut11_check :
    VG.AArch64.Straight.check (lanes 64 7) VG.Proof.CmacTripleDes.AArch64.oCfg (linExt 2) (pOut .x11) (linEnvC (VG.Proof.CmacTripleDes.AArch64.pIns .x11) VG.Proof.CmacTripleDes.AArch64.maskConsts)
      (linPost 7 [(.x11, VG.Proof.CmacTripleDes.AArch64.pG)]) = true := by
  lit_decide

theorem pOut12_check :
    VG.AArch64.Straight.check (lanes 64 7) VG.Proof.CmacTripleDes.AArch64.oCfg (linExt 2) (pOut .x12) (linEnvC (VG.Proof.CmacTripleDes.AArch64.pIns .x12) VG.Proof.CmacTripleDes.AArch64.maskConsts)
      (linPost 7 [(.x12, VG.Proof.CmacTripleDes.AArch64.pG)]) = true := by
  lit_decide

theorem pOut11_masks :
    maskConsts.all (fun p => (pOut .x11).all fun i => dstOf i != some p.1) = true := by
  lit_decide

theorem pOut12_masks :
    maskConsts.all (fun p => (pOut .x12).all fun i => dstOf i != some p.1) = true := by
  lit_decide

/-- The registers `pOut` keeps. -/
def pKept : List Reg := [.x1, .x2, .x3, .x4, .x5, .x10, .x14, .x15, .x16]

theorem pOut11_kept : (.x12 :: VG.Proof.CmacTripleDes.AArch64.pKept).all (fun r => (pOut .x11).all fun i => dstOf i != some r) = true := by
  lit_decide

theorem pOut12_kept : (.x11 :: VG.Proof.CmacTripleDes.AArch64.pKept).all (fun r => (pOut .x12).all fun i => dstOf i != some r) = true := by
  lit_decide

theorem pOut11_v : (pOut .x11).all (fun i => vdstOf i == none) = true := by lit_decide
theorem pOut12_v : (pOut .x12).all (fun i => vdstOf i == none) = true := by lit_decide

theorem pOut_ok (s : VG.AArch64.State) {a b : Reg} (hab : (a = .x11 ∧ b = .x12) ∨ (a = .x12 ∧ b = .x11))
    (hm : VG.Proof.CmacTripleDes.AArch64.Masks s) :
    ∃ s', runBlock isa (pOut a) s = some s' ∧
      (∀ p < 64, (s'.gpr a).getLsbD p =
        ((match ySrc p with | some q => (s.gpr .x5).getLsbD q | none => false) ^^ (s.gpr a).getLsbD p)) ∧
      (∀ r ∈ b :: VG.Proof.CmacTripleDes.AArch64.pKept, s'.gpr r = s.gpr r) ∧ VG.Proof.CmacTripleDes.AArch64.Masks s' ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let W (i : Nat) : BitVec 64 := if i = 0 then s.gpr .x5 else s.gpr a
  have go : ∀ (hchk : VG.AArch64.Straight.check (lanes 64 7) VG.Proof.CmacTripleDes.AArch64.oCfg (linExt 2) (pOut a) (linEnvC (VG.Proof.CmacTripleDes.AArch64.pIns a) VG.Proof.CmacTripleDes.AArch64.maskConsts)
        (linPost 7 [(a, VG.Proof.CmacTripleDes.AArch64.pG)]) = true)
      (hkept : (b :: VG.Proof.CmacTripleDes.AArch64.pKept).all (fun r => (pOut a).all fun i => dstOf i != some r) = true)
      (hmk : maskConsts.all (fun p => (pOut a).all fun i => dstOf i != some p.1) = true)
      (hv : (pOut a).all (fun i => vdstOf i == none) = true),
      ∃ s', runBlock isa (pOut a) s = some s' ∧
      (∀ p < 64, (s'.gpr a).getLsbD p =
        ((match ySrc p with | some q => (s.gpr .x5).getLsbD q | none => false) ^^ (s.gpr a).getLsbD p)) ∧
      (∀ r ∈ b :: VG.Proof.CmacTripleDes.AArch64.pKept, s'.gpr r = s.gpr r) ∧ VG.Proof.CmacTripleDes.AArch64.Masks s' ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    intro hchk hkept hmk hv
    obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_okC hchk (VG.Proof.CmacTripleDes.AArch64.oCfg_ok s) W
      (fun r i hri => by
        simp only [VG.Proof.CmacTripleDes.AArch64.pIns, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
        rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
      hm (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.AArch64.oCfg]))
    refine ⟨s', hs', fun p hp => ?_, fun r hr => hoth r (List.all_eq_true.mp hkept r hr),
      hm.congr fun p hp => hoth p.1 (List.all_eq_true.mp hmk p hp), ?_, ?_, hrd, hwr, hsp⟩
    · rw [hout a VG.Proof.CmacTripleDes.AArch64.pG (by simp) p hp, VG.Proof.CmacTripleDes.AArch64.pG]
      split
      · rename_i q hq
        have hq64 : q < 64 := VG.Proof.CmacTripleDes.AArch64.ySrc_lt hp hq
        simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, W,
          Nat.div_eq_of_lt hq64, Nat.mod_eq_of_lt hq64, show (64 + p) / 64 = 1 by omega,
          show (64 + p) % 64 = p by omega, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]
      · simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, W, Bool.false_xor,
          show (64 + p) / 64 = 1 by omega, show (64 + p) % 64 = p by omega,
          show (1 : Nat) ≠ 0 by decide, ite_false]
    · exact runBlock_v hv hs'
    · exact VG.Proof.CmacTripleDes.AArch64.frame_oCfg hfr
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact go VG.Proof.CmacTripleDes.AArch64.pOut11_check VG.Proof.CmacTripleDes.AArch64.pOut11_kept VG.Proof.CmacTripleDes.AArch64.pOut11_masks VG.Proof.CmacTripleDes.AArch64.pOut11_v
  · exact go VG.Proof.CmacTripleDes.AArch64.pOut12_check VG.Proof.CmacTripleDes.AArch64.pOut12_kept VG.Proof.CmacTripleDes.AArch64.pOut12_masks VG.Proof.CmacTripleDes.AArch64.pOut12_v

/-! ## The round -/

theorem runBlock_append (a b : List Instr) (s : VG.AArch64.State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

theorem xSrc_rot_lt : ∀ p < 64, (xSrc p + 32 - rot) % 32 < 32 := by decide

/-- The bit of `y` that `P` takes for a spread bit: box `i`'s output bit `q`. -/
theorem y_bit {y : BitVec 64} (I : Nat → BitVec 8) (T : Nat → BitVec 8)
    (hy : ∀ l < 8, y.extractLsb' (8 * l) 8 = T (I l).toNat) {i q : Nat} (hi : i < 8)
    (hpos : posOf i q < 8) :
    y.getLsbD (8 * laneOf i + posOf i q) = (T (I (laneOf i)).toNat).getLsbD (posOf i q) := by
  rw [← hy _ (VG.Proof.CmacTripleDes.AArch64.laneOf_lt i hi), BitVec.getLsbD_extractLsb', decide_eq_true hpos, Bool.true_and]

theorem posOf_lt : ∀ i < 8, ∀ q < 4, posOf i q < 8 := by decide

/-- One round: `a := a ⊕ f(b, K)`, spread, with the spread round key at
`x10`, moving it to the next. -/
theorem round_ok {s : VG.AArch64.State} {a b : Reg} (hab : (a = .x11 ∧ b = .x12) ∨ (a = .x12 ∧ b = .x11))
    (down : Bool) (hc : VG.Proof.CmacTripleDes.AArch64.Consts s) (hm : VG.Proof.CmacTripleDes.AArch64.Masks s) (hk : InRegions (s.rd ++ s.wr) (s.gpr .x10) 8)
    {l r : BitVec 32} {K : BitVec 64} (hl : s.gpr a = VG.Proof.CmacTripleDes.AArch64.spreadW l) (hr : s.gpr b = VG.Proof.CmacTripleDes.AArch64.spreadW r)
    (hK : s.mem.readW (s.gpr .x10) 64 = VG.Proof.CmacTripleDes.AArch64.spread K) :
    ∃ s', runBlock isa (round a b down) s = some s' ∧
      s'.gpr a = VG.Proof.CmacTripleDes.AArch64.spreadW (l ^^^ Spec.TripleDes.roundFunction r (K.setWidth 48)) ∧
      s'.gpr .x10 = (if down then s.gpr .x10 - 8 else s.gpr .x10 + 8) ∧
      (∀ g ∈ b :: [.x1, .x2, .x3, .x4, .x14, .x15, .x16], s'.gpr g = s.gpr g) ∧
      VG.Proof.CmacTripleDes.AArch64.Consts s' ∧ VG.Proof.CmacTripleDes.AArch64.Masks s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hb5 : b ≠ .x5 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hb10 : b ≠ .x10 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have ha5 : a ≠ .x5 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have ha10 : a ≠ .x10 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  obtain ⟨s₁, h₁, i₀, i₁, i₂, i₃, x10₁, g₁, v₁, m₁, rd₁, wr₁, sp₁⟩ := VG.Proof.CmacTripleDes.AArch64.sIn_ok s hb5 hb10 down hk hc
  have hc₁ : VG.Proof.CmacTripleDes.AArch64.Consts s₁ := hc.congr v₁
  let I : Nat → BitVec 8 := fun e => vbyte (s₁.v .v0) e
  obtain ⟨s₂, h₂, y₂, g₂, v₂, m₂, rd₂, wr₂, sp₂⟩ := VG.Proof.CmacTripleDes.AArch64.sOut_ok (s := s₁) I (fun _ _ => rfl)
    (fun e he => i₁ e he) (fun e he => i₂ e he) (fun e he => i₃ e he)
  have hc₂ : VG.Proof.CmacTripleDes.AArch64.Consts s₂ := hc₁.congr v₂
  have hm₂ : VG.Proof.CmacTripleDes.AArch64.Masks s₂ := hm.congr fun p hp => by
    obtain ⟨n5, n10, -⟩ := VG.Proof.CmacTripleDes.AArch64.maskRegs_ne p hp
    rw [g₂ _ n5, g₁ _ n5 n10]
  obtain ⟨s₃, h₃, a₃, k₃, hm₃, v₃, m₃, rd₃, wr₃, sp₃⟩ := VG.Proof.CmacTripleDes.AArch64.pOut_ok s₂ hab hm₂
  have hc₃ : VG.Proof.CmacTripleDes.AArch64.Consts s₃ := hc₂.congr fun w _ _ _ _ => by rw [v₃]
  have a₂ : s₂.gpr a = VG.Proof.CmacTripleDes.AArch64.spreadW l := by rw [g₂ a ha5, g₁ a ha5 ha10, hl]
  -- The S-boxes' outputs.
  have hy : ∀ l' < 8, (s₂.gpr .x5).extractLsb' (8 * l') 8 = sTable (I l').toNat := by
    intro l' hl'
    rw [y₂ l' hl', hc₁.tab _ (I l').isLt]
  have hI : ∀ i < 8, (I (laneOf i)).toNat = 2 ^ 6 * boxTable i + (chunk r (K.setWidth 48) i).toNat := by
    intro i hi
    have hL := VG.Proof.CmacTripleDes.AArch64.laneOf_lt i hi
    simp only [I]
    rw [i₀ _ hL, hK, hr, VG.Proof.CmacTripleDes.AArch64.index_byte K r hL, VG.Proof.CmacTripleDes.AArch64.boxOf_laneOf i hi, BitVec.toNat_ofNat]
    have := (chunk r (K.setWidth 48) i).isLt
    have := VG.Proof.CmacTripleDes.AArch64.tableOf_lt i hi
    omega
  refine ⟨s₃, ?_, ?_, ?_, fun g hg => ?_, hc₃, hm₃, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], by rw [sp₃, sp₂, sp₁]⟩
  · rw [round, runBlock_cat_some (runBlock_cat_some h₁ h₂) h₃]
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [a₃ p hp, a₂, VG.Proof.CmacTripleDes.AArch64.getLsbD_spreadW _ hp, VG.Proof.CmacTripleDes.AArch64.getLsbD_spreadW _ hp]
    have hj := VG.Proof.CmacTripleDes.AArch64.xSrc_rot_lt p hp
    cases hx : xBit p
    · have : ySrc p = none := by simp [ySrc, hx]
      rw [this]; simp
    · rw [VG.Proof.CmacTripleDes.AArch64.ySrc_eq hx, BitVec.getLsbD_xor, Bool.true_and, Bool.true_and,
        getLsbD_roundFunction r _ hj]
      dsimp only
      have hu := VG.Proof.CmacTripleDes.AArch64.pSrc_lt _ hj
      have hi : 7 - pSrc ((xSrc p + 32 - rot) % 32) / 4 < 8 := by omega
      have hq : pSrc ((xSrc p + 32 - rot) % 32) % 4 < 4 := Nat.mod_lt _ (by decide)
      rw [VG.Proof.CmacTripleDes.AArch64.y_bit I sTable hy hi (VG.Proof.CmacTripleDes.AArch64.posOf_lt _ hi _ hq), hI _ hi,
        VG.Proof.CmacTripleDes.AArch64.sTable_bit _ hi _ (chunk r (K.setWidth 48) _).isLt _ hq, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, Bool.xor_comm]
  · rw [k₃ .x10 (by simp [VG.Proof.CmacTripleDes.AArch64.pKept]), g₂ .x10 (by decide), x10₁]
  · have hg' : g ∈ b :: VG.Proof.CmacTripleDes.AArch64.pKept := by
      simp only [VG.Proof.CmacTripleDes.AArch64.pKept, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
      rcases hg with h | h | h | h | h | h | h | h <;> simp [h]
    have h5 : g ≠ .x5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> first | exact hb5 | decide
    have h10 : g ≠ .x10 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> first | exact hb10 | decide
    rw [k₃ g hg', g₂ g h5, g₁ g h5 h10]

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Spread`. -/
section

/-!
# DES on AArch64: spreading the round keys

`spreadBody` spreads two round keys at a time: `v0` holds them, `v1`–`v3`
the same shifted right by 2, 4 and 6 bits (in each 64-bit half), and a
`tbl` of the four gathers, for each byte of the result, the byte of a
shifted copy whose low six bits are its box's bits of the key
(`gather_facts`); masking those and XORing the tables' numbers into the
top two bits gives the two spread keys (`spreadV_ok`).
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Bitslice
  VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64 VG.Impl.Tbl.AArch64 VG.Proof.CmacTripleDes

/-- Byte `e` of the gathering index: below 64, in the half of its key, at
the byte and the shift (`2 k`, in register `v k`) of its box's bits. -/
theorem gather_facts : ∀ e < 16,
    (gatherIndex e).toNat < 64 ∧ (gatherIndex e).toNat % 16 / 8 = e / 8 ∧
      8 * ((gatherIndex e).toNat % 8) + 2 * ((gatherIndex e).toNat / 16) =
        6 * (7 - VG.Proof.CmacTripleDes.AArch64.boxOf (e % 8)) := by
  decide

/-- The vector part of `spreadBody`. -/
def spreadV : List Instr :=
  [.vop (.shift .ushr .d2 .v1 .v0 2), .vop (.shift .ushr .d2 .v2 .v0 4),
   .vop (.shift .ushr .d2 .v3 .v0 6), .vop (.tblN false 4 .v4 .v0 .v5),
   .vop (.logic .and .v4 .v4 .v6), .vop (.logic .eor .v4 .v4 .v7)]

/-- `x` shifted right by `2 k` in each 64-bit half. -/
def shr2 (x : BitVec 128) (k : Nat) : BitVec 128 :=
  ofVDwords (vdword x 0 >>> (2 * k)) (vdword x 1 >>> (2 * k))

theorem getLsbD_ofVDwords (a b : BitVec 64) {h j : Nat} (hh : h < 2) (hj : j < 64) :
    (ofVDwords a b).getLsbD (64 * h + j) = if h = 0 then a.getLsbD j else b.getLsbD j := by
  simp only [ofVDwords, BitVec.getLsbD_append]
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · simp [hj]
  · simp [show ¬ 64 + j < 64 by omega]

theorem getLsbD_vdword (x : BitVec 128) {h j : Nat} (hj : j < 64) :
    (vdword x h).getLsbD j = x.getLsbD (64 * h + j) := by
  simp [vdword, hj, Nat.add_comm]

theorem getLsbD_shr2 (x : BitVec 128) (k : Nat) {h j : Nat} (hh : h < 2) (hj : j < 64) :
    (VG.Proof.CmacTripleDes.AArch64.shr2 x k).getLsbD (64 * h + j) = (decide (2 * k + j < 64) && x.getLsbD (64 * h + (2 * k + j))) := by
  rw [VG.Proof.CmacTripleDes.AArch64.shr2, VG.Proof.CmacTripleDes.AArch64.getLsbD_ofVDwords _ _ hh hj]
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
  · simp only [BitVec.getLsbD_ushiftRight, ite_true, ite_false, show (1 : Nat) ≠ 0 by decide]
    by_cases h' : 2 * k + j < 64
    · rw [VG.Proof.CmacTripleDes.AArch64.getLsbD_vdword _ h', decide_eq_true h', Bool.true_and]
    · rw [decide_eq_false h', Bool.false_and, BitVec.getLsbD_of_ge _ _ (by omega)]

theorem shr2_zero (x : BitVec 128) : VG.Proof.CmacTripleDes.AArch64.shr2 x 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := VG.Proof.CmacTripleDes.AArch64.getLsbD_shr2 x 0 (h := i / 64) (j := i % 64) (by omega) (by omega)
  rw [show 64 * (i / 64) + i % 64 = i by omega, show 64 * (i / 64) + (2 * 0 + i % 64) = i by omega,
    decide_eq_true (by omega), Bool.true_and] at this
  exact this

/-- The table registers of the gathering `tbl`: `v0`–`v3`. -/
theorem repeat_v0 : ∀ k < 4, Nat.repeat VReg.succ k .v0 = [VReg.v0, .v1, .v2, .v3].getD k .v0 := by
  decide

theorem spreadV_ok (s : VG.AArch64.State) (hG : s.v .v5 = ofVBytes gatherIndex) (hM : s.v .v6 = bc 63)
    (hO : s.v .v7 = ofVDwords offsets offsets) :
    ∃ s', runBlock isa VG.Proof.CmacTripleDes.AArch64.spreadV s = some s' ∧
      s'.v .v4 = ofVDwords (VG.Proof.CmacTripleDes.AArch64.spread (vdword (s.v .v0) 0)) (VG.Proof.CmacTripleDes.AArch64.spread (vdword (s.v .v0) 1)) ∧
      (∀ w, w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → s'.v w = s.v w) ∧
      s' = { s with v := s'.v } := by
  let x := s.v .v0
  let s₁ := s.setV .v1 (VG.Proof.CmacTripleDes.AArch64.shr2 x 1)
  let s₂ := s₁.setV .v2 (VG.Proof.CmacTripleDes.AArch64.shr2 x 2)
  let s₃ := s₂.setV .v3 (VG.Proof.CmacTripleDes.AArch64.shr2 x 3)
  let T : BitVec 128 := ofVBytes fun i =>
    let idx := (vbyte (s₃.v .v5) i).toNat
    if idx < 16 * 4 then tableByte s₃.v .v0 idx else 0
  let s₄ := s₃.setV .v4 T
  let s₅ := s₄.setV .v4 (s₄.v .v4 &&& s₄.v .v6)
  let s₆ := s₅.setV .v4 (s₅.v .v4 ^^^ s₅.v .v7)
  have r₃ : ∀ k < 4, s₃.v ([VReg.v0, .v1, .v2, .v3].getD k .v0) = VG.Proof.CmacTripleDes.AArch64.shr2 x k := by
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · simp only [List.getD_cons_zero, s₃, s₂, s₁, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1),
        VG.Proof.CmacTripleDes.AArch64.shr2_zero]
      rfl
    · simp only [s₃, s₂, s₁]; simp [State.setV]
    · simp only [s₃, s₂]; simp [State.setV]
    · simp only [s₃]; simp [State.setV]
  have v5₃ : s₃.v .v5 = ofVBytes gatherIndex := by
    simp only [s₃, s₂, s₁, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v3),
      v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v1), hG]
  have v6₄ : s₄.v .v6 = bc 63 := by
    simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v4),
      v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v3), v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v2),
      v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v1), hM]
  have v7₅ : s₅.v .v7 = ofVDwords offsets offsets := by
    simp only [s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v4),
      v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v3), v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v2),
      v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v1), hO]
  -- Only `v` changes (`rfl` would unify the states field by field, trying eta on each).
  have hv : ∀ (t : VG.AArch64.State) (r : VReg) (y : BitVec 128), t = { s with
                                                                    v := t.v } →
      t.setV r y = { s with v := (t.setV r y).v } := by
    intro t r y h; rw [h]; rfl
  refine ⟨s₆, ?_, ?_, fun w h1 h2 h3 h4 => ?_,
    hv _ _ _ (hv _ _ _ (hv _ _ _ (hv _ _ _ (hv _ _ _ (hv _ _ _ rfl)))))⟩
  · rw [VG.Proof.CmacTripleDes.AArch64.spreadV]
    rfl
  · have a₆ : s₆.v .v4 = s₅.v .v4 ^^^ s₅.v .v7 := v_setV_self _ _ _
    have a₅ : s₅.v .v4 = s₄.v .v4 &&& s₄.v .v6 := v_setV_self _ _ _
    have a₄ : s₄.v .v4 = T := v_setV_self _ _ _
    rw [a₆, v7₅, a₅, v6₄, a₄]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    -- In the half `h` of the key, position `j`, byte `e`, bit `t`.
    obtain ⟨h, j, hh, hj, rfl⟩ : ∃ h j, h < 2 ∧ j < 64 ∧ i = 64 * h + j :=
      ⟨i / 64, i % 64, by omega, by omega, by omega⟩
    have he : 8 * h + j / 8 < 16 := by omega
    obtain ⟨g64, ghalf, gpos⟩ := VG.Proof.CmacTripleDes.AArch64.gather_facts (8 * h + j / 8) he
    have hT : T.getLsbD (64 * h + j) = (vbyte (VG.Proof.CmacTripleDes.AArch64.shr2 x ((gatherIndex (8 * h + j / 8)).toNat / 16))
        ((gatherIndex (8 * h + j / 8)).toNat % 16)).getLsbD (j % 8) := by
      have := getLsbD_ofVBytes (fun i =>
        let idx := (vbyte (s₃.v .v5) i).toNat
        if idx < 16 * 4 then tableByte s₃.v .v0 idx else 0) he (show j % 8 < 8 by omega)
      rw [show 8 * (8 * h + j / 8) + j % 8 = 64 * h + j by omega] at this
      rw [show T = _ from rfl, this]
      simp only
      rw [v5₃, vbyte_ofVBytes _ he, ite_eq_left (by omega), tableByte,
        VG.Proof.CmacTripleDes.AArch64.repeat_v0 _ (by omega), r₃ _ (by omega)]
    have hbc : (bc 63).getLsbD (64 * h + j) = decide (j % 8 < 6) := by
      have := getLsbD_ofVBytes (fun _ => (63 : BitVec 8)) he (show j % 8 < 8 by omega)
      rw [show 8 * (8 * h + j / 8) + j % 8 = 64 * h + j by omega] at this
      rw [bc, this]
      have : ∀ t < 8, (63 : BitVec 8).getLsbD t = decide (t < 6) := by decide
      exact this _ (by omega)
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, hT, hbc, VG.Proof.CmacTripleDes.AArch64.getLsbD_ofVDwords _ _ hh hj,
      VG.Proof.CmacTripleDes.AArch64.getLsbD_ofVDwords _ _ hh hj]
    have hj8 : j = 8 * (j / 8) + j % 8 := by omega
    have hsp : ∀ (K : BitVec 64), (VG.Proof.CmacTripleDes.AArch64.spread K).getLsbD j =
        if j % 8 < 6 then K.getLsbD (6 * (7 - VG.Proof.CmacTripleDes.AArch64.boxOf (j / 8)) + j % 8) else offsets.getLsbD j := by
      intro K
      rw [hj8, VG.Proof.CmacTripleDes.AArch64.getLsbD_spread K (by omega) (by omega), VG.Proof.CmacTripleDes.AArch64.offsets_bits _ (by omega) _ (by omega)]
      simp only [show (8 * (j / 8) + j % 8) % 8 = j % 8 by omega,
        show (8 * (j / 8) + j % 8) / 8 = j / 8 by omega]
      by_cases h6 : j % 8 < 6
      · simp [h6]
      · simp [h6, show 6 ≤ j % 8 by omega]
    have hoff : j % 8 < 6 → offsets.getLsbD j = false := by
      intro h6
      rw [hj8, VG.Proof.CmacTripleDes.AArch64.offsets_bits _ (by omega) _ (by omega), decide_eq_false (by omega), Bool.false_and]
    have hbox : (8 * h + j / 8) % 8 = j / 8 := by omega
    rw [hbox] at gpos
    -- The gathered bit.
    have hg : j % 8 < 6 → (vbyte (VG.Proof.CmacTripleDes.AArch64.shr2 x ((gatherIndex (8 * h + j / 8)).toNat / 16))
        ((gatherIndex (8 * h + j / 8)).toNat % 16)).getLsbD (j % 8) =
        (vdword x h).getLsbD (6 * (7 - VG.Proof.CmacTripleDes.AArch64.boxOf (j / 8)) + j % 8) := by
      intro h6
      rw [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true (by omega), Bool.true_and,
        show 8 * ((gatherIndex (8 * h + j / 8)).toNat % 16) + j % 8 =
          64 * h + (8 * ((gatherIndex (8 * h + j / 8)).toNat % 8) + j % 8) by omega,
        VG.Proof.CmacTripleDes.AArch64.getLsbD_shr2 _ _ hh (by omega), decide_eq_true (by omega), Bool.true_and,
        VG.Proof.CmacTripleDes.AArch64.getLsbD_vdword _ (by omega)]
      congr 1
      omega
    have hite : ∀ (a b : BitVec 64), (if h = 0 then a.getLsbD j else b.getLsbD j) =
        ([a, b].getD h 0).getLsbD j := by
      intro a b; rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl
    have hvd : ∀ h' < 2, vdword x h' = [vdword x 0, vdword x 1].getD h' 0 := by
      intro h' hh'; rcases (by omega : h' = 0 ∨ h' = 1) with rfl | rfl <;> rfl
    have hsp' : ([VG.Proof.CmacTripleDes.AArch64.spread (vdword x 0), VG.Proof.CmacTripleDes.AArch64.spread (vdword x 1)].getD h 0) = VG.Proof.CmacTripleDes.AArch64.spread (vdword x h) := by
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl
    rw [hite, hite, hsp', show ([offsets, offsets].getD h 0) = offsets by
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl, hsp]
    by_cases h6 : j % 8 < 6
    · rw [decide_eq_true h6, Bool.and_true, hg h6, hoff h6, Bool.xor_false, ite_eq_left h6]
    · rw [decide_eq_false h6, Bool.and_false, Bool.false_xor, ite_eq_right h6]
  · simp only [s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h4, v_setV_of_ne _ _ h3,
      v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h1]

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Block`. -/
section

/-!
# TDEA on AArch64: the passes and the block

`block` encrypts the 64-bit block in `x5` with the key schedule at `x14`
(`block_ok`): it spreads the 48 round keys into the scratch buffer at `x15`
(`spreadLoop_ok`), loads the tables and the constants and applies `IP`,
leaving `L` and `R` spread in `x11` and `x12` (`setup_ok`), runs three passes
of sixteen rounds (`pass_ok`, two rounds per iteration, the spread round
keys from `x10`, moving down in the middle pass, the halves exchanged after
the first two), and applies `IP⁻¹`. Only the scratch buffer's first 384
bytes change.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Straight VG.AArch64.Tbl VG.Bitslice VG.Impl.CmacTripleDes
  VG.Impl.CmacTripleDes.AArch64 VG.Impl.Tbl.AArch64 VG.Proof.CmacTripleDes

theorem ofNat_ne_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = !decide (x = 0) := by
  have : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this
    · intro he; rw [he]; rfl
  rw [bne, this]

theorem eval_nonzero {s : VG.AArch64.State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x r) s = some !decide (x = 0) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, VG.Proof.CmacTripleDes.AArch64.ofNat_ne_zero hx]

theorem eval_zero {s : VG.AArch64.State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.zero .x r) s = some (decide (x = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := VG.Proof.CmacTripleDes.AArch64.ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all


/-- What the block needs: the key schedule at `x14` readable, and the first
456 bytes of the scratch buffer at `x15` writable, apart from it. -/
structure BlockPre (s : VG.AArch64.State) : Prop where
  sched : ∃ R ∈ s.rd ++ s.wr, R.base = s.gpr .x14 ∧ 384 ≤ R.len ∧ R.len < 2 ^ 64
  scr : ∃ R ∈ s.wr, R.base = s.gpr .x15 ∧ 456 ≤ R.len ∧ R.len < 2 ^ 64
  disj : Region.Disjoint ⟨s.gpr .x15, 456⟩ ⟨s.gpr .x14, 384⟩

/-- The spread round keys' slots. -/
abbrev xR (s₀ : VG.AArch64.State) : Region := ⟨s₀.gpr .x15, 384⟩

/-- The registers of the functions that the block keeps (with `x14` and `x15`). -/
def outer : List Reg := [.x1, .x2, .x3, .x4]

/-- What the block keeps. -/
structure Same (s₀ s : VG.AArch64.State) : Prop where
  x15 : s.gpr .x15 = s₀.gpr .x15
  keep : ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.outer, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacTripleDes.AArch64.xR s₀] s₀.mem s.mem

theorem Same.refl (s : VG.AArch64.State) : VG.Proof.CmacTripleDes.AArch64.Same s s := ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The key schedule. -/
abbrev sch (s₀ : VG.AArch64.State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x14)

/-- The spread round keys, in the scratch buffer. -/
def Keys (s₀ : VG.AArch64.State) (m : Mem) (n : Nat) : Prop :=
  ∀ i < n, m.readW (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 64 = VG.Proof.CmacTripleDes.AArch64.spread ((VG.Proof.CmacTripleDes.AArch64.sch s₀).getD i 0)

theorem BlockPre.slot {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {s : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.Same s₀ s) {d n : Nat}
    (hd : d + n ≤ 384) : InRegions s.wr (s₀.gpr .x15 + BitVec.ofNat 64 d) n := by
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  rw [h.wr]
  exact ⟨X, hX, by rw [← hXb]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem BlockPre.key {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {s : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.Same s₀ s) {d n : Nat}
    (hd : d + n ≤ 384) : InRegions (s.rd ++ s.wr) (s₀.gpr .x14 + BitVec.ofNat 64 d) n := by
  obtain ⟨R, hR, hRb, hRl, hRw⟩ := hp.sched
  rw [h.rd, h.wr]
  exact ⟨R, hR, by rw [← hRb]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- The key schedule is unchanged while only the scratch buffer changes. -/
theorem sched_word {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {m : Mem} (hf : Frame [VG.Proof.CmacTripleDes.AArch64.xR s₀] s₀.mem m) {d : Nat}
    (hd : d + 8 ≤ 384) :
    m.readW (s₀.gpr .x14 + BitVec.ofNat 64 d) 64 = s₀.mem.readW (s₀.gpr .x14 + BitVec.ofNat 64 d) 64 :=
  (hf.readW (r := ⟨s₀.gpr .x14 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.disj.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ hd)).symm)
    (by decide))

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## Memory -/

theorem vdword_read (m : Mem) (a : Addr) {h : Nat} (hh : h < 2) :
    vdword (m.read a 16) h = m.readW (a + BitVec.ofNat 64 (8 * h)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [VG.Proof.CmacTripleDes.AArch64.getLsbD_vdword _ hi, getLsbD_read m 16 a _ (by omega), getLsbD_readW64 _ _ hi,
    BitVec.add_assoc, ← BitVec.ofNat_add, show (64 * h + i) / 8 = 8 * h + i / 8 by omega,
    show (64 * h + i) % 8 = i % 8 by omega]

theorem readW_write16 (m : Mem) (a : Addr) (v : BitVec 128) {h : Nat} (hh : h < 2) :
    (m.write a 16 v).readW (a + BitVec.ofNat 64 (8 * h)) 64 = vdword v h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_readW64 _ _ hi, VG.Proof.CmacTripleDes.AArch64.getLsbD_vdword _ hi, BitVec.add_assoc, ← BitVec.ofNat_add, Mem.write,
    Mem.sub_ofNat_toNat a (by omega), ite_eq_left (by omega)]
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-! ## Spreading the round keys -/

theorem exec_mov {s : VG.AArch64.State} {d n : Reg} : exec (mov d n) s = some (s.write .x d (s.gpr n)) := by
  rw [mov, exec_addImm_x (by decide)]
  simp [State.read]

theorem exec_movz_x {s : VG.AArch64.State} {d : Reg} {imm : BitVec 16} {hw : Nat} (h : hw < 4) :
    exec (.movz .x d imm hw) s = some (s.write .x d (imm.setWidth 64 <<< (16 * hw))) := by
  simp only [exec, Size.bits, show 16 * hw < 64 by omega, ite_true]

theorem exec_dupd (s : VG.AArch64.State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

/-- After `m` pairs of keys. -/
structure SInv (s₀ : VG.AArch64.State) (m : Nat) (s : VG.AArch64.State) : Prop where
  same : VG.Proof.CmacTripleDes.AArch64.Same s₀ s
  x5 : s.gpr .x5 = s₀.gpr .x5
  x14 : s.gpr .x14 = s₀.gpr .x14
  x6 : s.gpr .x6 = s₀.gpr .x14 + BitVec.ofNat 64 (16 * m)
  x7 : s.gpr .x7 = s₀.gpr .x15 + BitVec.ofNat 64 (16 * m)
  x16 : s.gpr .x16 = BitVec.ofNat 64 (24 - m)
  g : s.v .v5 = ofVBytes gatherIndex
  c63 : s.v .v6 = bc 63
  off : s.v .v7 = ofVDwords offsets offsets
  keys : VG.Proof.CmacTripleDes.AArch64.Keys s₀ s.mem (2 * m)

theorem spreadPre_eq : spreadPre = const128 .v5 (ofVBytes gatherIndex) ++
    (([.movz .x .x6 63 0, .vop (.dup .b16 .v6 .x6)] : List Instr) ++ (const64 .x6 offsets ++
      ([.vop (.dup .d2 .v7 .x6), mov .x6 .x14, mov .x7 .x15, .movz .x .x16 24 0] : List Instr))) := by
  simp only [spreadPre, List.append_assoc]

theorem spreadPre_ok (s₀ : VG.AArch64.State) : WP isa (.block spreadPre) s₀ (VG.Proof.CmacTripleDes.AArch64.SInv s₀ 0) := by
  rw [VG.Proof.CmacTripleDes.AArch64.spreadPre_eq, WP.block_append_iff]
  refine WP.mono (const128_ok s₀ .v5 _) fun a ⟨a5, av, ag, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  let b := (a.write .x .x6 ((63 : BitVec 16).setWidth 64 <<< (16 * 0)))
  let b' := b.setV .v6 (bc ((b.gpr .x6).setWidth 8))
  refine WP.of_runBlock ⟨b', by
    rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_movz_x (by decide), runStep_some, runBlock_cons, exec_dupb, runStep_some,
      runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b' .x6 offsets) fun c ⟨c6, cg, ce⟩ => ?_
  let d₁ := c.setV .v7 (ofVDwords (c.gpr .x6) (c.gpr .x6))
  let d₂ := d₁.write .x .x6 (d₁.gpr .x14)
  let d₃ := d₂.write .x .x7 (d₂.gpr .x15)
  let d₄ := d₃.write .x .x16 ((24 : BitVec 16).setWidth 64 <<< (16 * 0))
  refine WP.of_runBlock ⟨d₄, by
    rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_dupd, runStep_some, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_cons,
      VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_movz_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have cv : c.v = b'.v := by rw [ce]
  have cmem : c.mem = s₀.mem := by rw [ce]; exact am
  have g14 : c.gpr .x14 = s₀.gpr .x14 := by
    rw [cg .x14 (by decide)]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x6)]
    exact ag .x14 (by decide) (by decide)
  have g15 : c.gpr .x15 = s₀.gpr .x15 := by
    rw [cg .x15 (by decide)]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x6)]
    exact ag .x15 (by decide) (by decide)
  have gout : ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.outer, c.gpr r = s₀.gpr r := by
    intro r hr
    have h6 : r ≠ .x6 := by simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h7 : r ≠ .x7 := by simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [cg r h6]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ h6]; exact ag r h6 h7
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega)⟩
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x7), gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x6),
      gpr_setV, g15]
  · have h6 : r ≠ .x6 := by simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h7 : r ≠ .x7 := by simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h16 : r ≠ .x16 := by simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ h16, gpr_write_of_ne _ _ _ h7,
      gpr_write_of_ne _ _ _ h6, gpr_setV, gout r hr]
  · simp only [d₄, d₃, d₂, d₁, sp_write, sp_setV]; rw [ce]; simp only [b', b, sp_setV, sp_write, asp]
  · simp only [d₄, d₃, d₂, d₁, rd_write, rd_setV]; rw [ce]; simp only [b', b, rd_setV, rd_write, ard]
  · simp only [d₄, d₃, d₂, d₁, wr_write, wr_setV]; rw [ce]; simp only [b', b, wr_setV, wr_write, awr]
  · simp only [d₄, d₃, d₂, d₁, mem_write, mem_setV, cmem]; exact Frame.refl _ _
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x7), gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x6),
      gpr_setV]
    rw [cg .x5 (by decide)]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x6)]
    exact ag .x5 (by decide) (by decide)
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x7), gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x6),
      gpr_setV, g14]
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x7), gpr_write_self, BitVec.setWidth_eq, gpr_setV, g14]
    simp
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x16), gpr_write_self,
      BitVec.setWidth_eq, gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x6), gpr_setV, g15]
    simp
  · simp only [d₄, gpr_write_self, BitVec.setWidth_eq]; decide
  · simp only [d₄, d₃, d₂, d₁, v_write, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v7), cv, b',
      v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v6), b, v_write, a5]
  · simp only [d₄, d₃, d₂, d₁, v_write, v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v7), cv, b',
      v_setV_self, b, gpr_write_self, BitVec.setWidth_eq]
    rfl
  · simp only [d₄, d₃, d₂, d₁, v_write, v_setV_self, c6]

theorem spreadBody_eq : spreadBody = ([.ldrq .v0 .x6 0] : List Instr) ++ VG.Proof.CmacTripleDes.AArch64.spreadV ++
    ([.strq .v4 .x7 0, .addImm .x .x6 .x6 16, .addImm .x .x7 .x7 16, .subImm .x .x16 .x16 1] : List Instr) :=
  rfl

theorem exec_ldrq0 (s : VG.AArch64.State) (t : VReg) (n : Reg) (h : InRegions (s.rd ++ s.wr) (s.gpr n) 16) :
    exec (.ldrq t n 0) s = some (s.setV t (s.mem.read (s.gpr n) 16)) := by
  simp only [exec, addr, show 0 % 16 = 0 from rfl, show 0 < 4096 * 16 by decide, and_self, ite_true,
    BitVec.add_zero, Option.bind_some, State.load, h, Option.map_some]

theorem exec_strq0 (s : VG.AArch64.State) (t : VReg) (n : Reg) (h : InRegions s.wr (s.gpr n) 16) :
    exec (.strq t n 0) s = some { s with mem := s.mem.write (s.gpr n) 16 (s.v t) } := by
  simp only [exec, addr, show 0 % 16 = 0 from rfl, show 0 < 4096 * 16 by decide, and_self, ite_true,
    BitVec.add_zero, Option.bind_some, State.store, h]

theorem spreadStep_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {m : Nat} (hm : m < 24) {s : VG.AArch64.State}
    (h : VG.Proof.CmacTripleDes.AArch64.SInv s₀ m s) : WP isa (.block spreadBody) s (VG.Proof.CmacTripleDes.AArch64.SInv s₀ (m + 1)) := by
  rw [VG.Proof.CmacTripleDes.AArch64.spreadBody_eq, WP.block_append_iff, WP.block_append_iff]
  have rk : InRegions (s.rd ++ s.wr) (s.gpr .x6) 16 := by
    rw [h.x6]; exact hp.key h.same (by omega)
  let s₁ := s.setV .v0 (s.mem.read (s.gpr .x6) 16)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_ldrq0 _ _ _ rk, runStep_some, runBlock_nil], ?_⟩
  obtain ⟨s₂, h₂, v4₂, v₂, e₂⟩ := VG.Proof.CmacTripleDes.AArch64.spreadV_ok s₁
    (by simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v0), h.g])
    (by simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v0), h.c63])
    (by simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v0), h.off])
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  have g₂ : s₂.gpr = s.gpr := by rw [e₂]; rfl
  have m₂ : s₂.mem = s.mem := by rw [e₂]; rfl
  have wr₂ : s₂.wr = s.wr := by rw [e₂]; rfl
  have rd₂ : s₂.rd = s.rd := by rw [e₂]; rfl
  have sp₂ : s₂.sp = s.sp := by rw [e₂]; rfl
  have ws : InRegions s₂.wr (s₂.gpr .x7) 16 := by
    rw [wr₂, g₂, h.x7]; exact hp.slot h.same (by omega)
  let V := s₂.v .v4
  let s₃ : VG.AArch64.State := { s₂ with
                              mem := s₂.mem.write (s₂.gpr .x7) 16 V }
  let s₄ := s₃.write .x .x6 (s₃.read .x .x6 + BitVec.ofNat _ 16)
  let s₅ := s₄.write .x .x7 (s₄.read .x .x7 + BitVec.ofNat _ 16)
  let s₆ := s₅.write .x .x16 (s₅.read .x .x16 - BitVec.ofNat _ 1)
  refine WP.of_runBlock ⟨s₆, by
    rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_strq0 _ _ _ ws, runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have g₆ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → s₆.gpr r = s.gpr r := by
    intro r h6 h7 h16
    simp only [s₆, s₅, s₄, gpr_write_of_ne _ _ _ h16, gpr_write_of_ne _ _ _ h7, gpr_write_of_ne _ _ _ h6]
    show s₂.gpr r = s.gpr r
    rw [g₂]
  have v₆ : s₆.v = s₂.v := rfl
  have mem₆ : s₆.mem = s.mem.write (s₀.gpr .x15 + BitVec.ofNat 64 (16 * m)) 16 V := by
    show s₂.mem.write (s₂.gpr .x7) 16 V = _
    rw [m₂, g₂, h.x7]
  have hK : ∀ hh < 2, vdword (s₁.v .v0) hh = (VG.Proof.CmacTripleDes.AArch64.sch s₀).getD (2 * m + hh) 0 := by
    intro hh hh2
    rw [show s₁.v .v0 = s.mem.read (s.gpr .x6) 16 from v_setV_self _ _ _, VG.Proof.CmacTripleDes.AArch64.vdword_read _ _ hh2, h.x6,
      Offset.add_add, scheduleAt_getD _ _ (by omega),
      show 16 * m + 8 * hh = 8 * (2 * m + hh) by omega]
    exact VG.Proof.CmacTripleDes.AArch64.sched_word hp h.same.frame (by omega)
  have outer_ne : ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.outer, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x16 := by
    intro r hr; simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₆ _ (by decide) (by decide) (by decide), h.same.x15]
  · obtain ⟨a, b, c⟩ := outer_ne r hr
    rw [g₆ r a b c, h.same.keep r hr]
  · show s₂.sp = _; rw [sp₂, h.same.sp]
  · show s₂.rd = _; rw [rd₂, h.same.rd]
  · show s₂.wr = _; rw [wr₂, h.same.wr]
  · rw [mem₆]
    exact h.same.frame.write (r := VG.Proof.CmacTripleDes.AArch64.xR s₀) (by simp) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [g₆ _ (by decide) (by decide) (by decide), h.x5]
  · rw [g₆ _ (by decide) (by decide) (by decide), h.x14]
  · simp only [s₆, s₅, s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x7), gpr_write_self, State.read,
      BitVec.setWidth_eq]
    show s₂.gpr .x6 + _ = _
    rw [g₂, h.x6, Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega]
  · simp only [s₆, s₅, gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x16), gpr_write_self, State.read,
      BitVec.setWidth_eq, s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x6)]
    show s₂.gpr .x7 + _ = _
    rw [g₂, h.x7, Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega]
  · simp only [s₆, gpr_write_self, State.read, BitVec.setWidth_eq, s₅,
      gpr_write_of_ne _ _ _ (by decide : Reg.x16 ≠ .x7), s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x16 ≠ .x6)]
    show s₂.gpr .x16 - _ = _
    rw [g₂, h.x16]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Size.bits]
    omega
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v0), h.g]
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v0), h.c63]
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v0), h.off]
  · intro i hi
    rw [mem₆]
    by_cases hnew : 2 * m ≤ i
    · have hh : i - 2 * m < 2 := by omega
      rw [show s₀.gpr .x15 + BitVec.ofNat 64 (8 * i) =
          s₀.gpr .x15 + BitVec.ofNat 64 (16 * m) + BitVec.ofNat 64 (8 * (i - 2 * m)) by
          rw [Offset.add_add]; congr 2; omega,
        VG.Proof.CmacTripleDes.AArch64.readW_write16 _ _ _ hh]
      show vdword (s₂.v .v4) _ = _
      have hK' : vdword (s₁.v .v0) (i - 2 * m) = (VG.Proof.CmacTripleDes.AArch64.sch s₀).getD i 0 := by
        rw [hK _ hh, show 2 * m + (i - 2 * m) = i by omega]
      rw [v4₂, ← hK']
      rcases (by omega : i - 2 * m = 0 ∨ i - 2 * m = 1) with e | e <;> rw [e]
      · rw [vdword_ofVDwords_0]
      · rw [vdword_ofVDwords_1]
    · have hsep : Mem.Sep (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 8
          (s₀.gpr .x15 + BitVec.ofNat 64 (16 * m)) 16 :=
        Offset.sep _ (by omega) (by omega) (by omega)
      rw [Mem.readW, Mem.read_write_sep hsep (by decide)]
      exact h.keys i (by omega)

theorem spreadLoop_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {s : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.SInv s₀ 0 s) :
    WP isa (.loop (.block spreadBody) (.nonzero .x .x16)) s (VG.Proof.CmacTripleDes.AArch64.SInv s₀ 24) := by
  refine WP.loop (M := isa) (body := .block spreadBody) (c := .nonzero .x .x16) (Q := VG.Proof.CmacTripleDes.AArch64.SInv s₀ 24)
    (fun (n : Nat) (t : VG.AArch64.State) => ∃ m, n = 24 - m ∧ m < 24 ∧ VG.Proof.CmacTripleDes.AArch64.SInv s₀ m t) ?_ 24 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨m, rfl, hm, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.spreadStep_ok hp hm ht) fun t' h' => ?_
  have ev := VG.Proof.CmacTripleDes.AArch64.eval_nonzero (r := .x16) (x := 24 - (m + 1)) (by omega) h'.x16
  by_cases hz : m + 1 = 24
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega, 24 - (m + 1), by omega, m + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- No memory. -/
theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

/-- `IP`'s halves, rotated and spread, into `x11` and `x12`, from `x5` (input word 0). -/
def ipG11 (p : Nat) : List Nat := if xBit p then [ipSrc (32 + (xSrc p + 32 - rot) % 32)] else []
def ipG12 (p : Nat) : List Nat := if xBit p then [ipSrc ((xSrc p + 32 - rot) % 32)] else []

theorem ip_check :
    VG.AArch64.Straight.check (lanes 64 6) VG.Proof.CmacTripleDes.AArch64.oCfg (linExt 1) ipCode (linEnv [(.x5, 0)])
      (linPost 6 [(.x11, VG.Proof.CmacTripleDes.AArch64.ipG11), (.x12, VG.Proof.CmacTripleDes.AArch64.ipG12)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into `x5`, from `R` spread in `x12` (input word 0) and `L`
spread in `x11` (input word 1). -/
def fpG (j : Nat) : List Nat :=
  if 32 ≤ fpSrc j then [xPos ((fpSrc j - 32 + rot) % 32)] else [64 + xPos ((fpSrc j + rot) % 32)]

theorem fp_check :
    VG.AArch64.Straight.check (lanes 64 7) VG.Proof.CmacTripleDes.AArch64.oCfg (linExt 2) fpCode (linEnv [(.x12, 0), (.x11, 1)]) (linPost 7 [(.x5, VG.Proof.CmacTripleDes.AArch64.fpG)]) = true := by
  lit_decide

def blockKept : List Reg := [.x1, .x2, .x3, .x4, .x10, .x14, .x15]

theorem ip_kept : blockKept.all (fun r => ipCode.all fun i => dstOf i != some r) = true := by lit_decide

theorem fp_kept : blockKept.all (fun r => fpCode.all fun i => dstOf i != some r) = true := by lit_decide

theorem fp_v : fpCode.all (fun i => vdstOf i == none) = true := by lit_decide

theorem fp_masks : maskConsts.all (fun p => fpCode.all fun i => dstOf i != some p.1) = true := by
  lit_decide

theorem ip_v : ipCode.all (fun i => vdstOf i == none) = true := by lit_decide

theorem ip_masks : maskConsts.all (fun p => ipCode.all fun i => dstOf i != some p.1) = true := by
  lit_decide

theorem xPos_facts : ∀ e < 32, xPos e < 64 ∧ xBit (xPos e) = true ∧ xSrc (xPos e) = e := by decide

theorem ip_ok (s : VG.AArch64.State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      s'.gpr .x11 = VG.Proof.CmacTripleDes.AArch64.spreadW (split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x5))).1 ∧
      s'.gpr .x12 = VG.Proof.CmacTripleDes.AArch64.spreadW (split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x5))).2 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ VG.Proof.CmacTripleDes.AArch64.blockKept, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.v = s.v ∧ (∀ p ∈ VG.Proof.CmacTripleDes.AArch64.maskConsts, s'.gpr p.1 = s.gpr p.1) := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.AArch64.ip_check (VG.Proof.CmacTripleDes.AArch64.oCfg_ok s) (fun _ => s.gpr .x5)
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.AArch64.oCfg]))
  refine ⟨s', hs', ?_, ?_, hrd, hwr, hsp, fun r hr => hoth r (List.all_eq_true.mp VG.Proof.CmacTripleDes.AArch64.ip_kept r hr),
    VG.Proof.CmacTripleDes.AArch64.frame_oCfg hfr, runBlock_v VG.Proof.CmacTripleDes.AArch64.ip_v hs', fun p hp => hoth p.1 (List.all_eq_true.mp VG.Proof.CmacTripleDes.AArch64.ip_masks p hp)⟩
  · apply BitVec.eq_of_getLsbD_eq; intro p hp
    have hj := VG.Proof.CmacTripleDes.AArch64.xSrc_rot_lt p hp
    rw [hout .x11 VG.Proof.CmacTripleDes.AArch64.ipG11 (by simp) p hp, VG.Proof.CmacTripleDes.AArch64.getLsbD_spreadW _ hp, VG.Proof.CmacTripleDes.AArch64.ipG11]
    cases hx : xBit p
    · simp
    · have hs := VG.Proof.CmacTripleDes.AArch64.ipSrc_lt (32 + (xSrc p + 32 - rot) % 32) (by omega)
      simp only [ite_true, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs,
        Bool.true_and, split, BitVec.getLsbD_setWidth, decide_eq_true hj,
        BitVec.getLsbD_ushiftRight]
      rw [getLsbD_permute _ _ (by decide) (show 32 + (xSrc p + 32 - rot) % 32 < 64 by omega)]
      rfl
  · apply BitVec.eq_of_getLsbD_eq; intro p hp
    have hj := VG.Proof.CmacTripleDes.AArch64.xSrc_rot_lt p hp
    rw [hout .x12 VG.Proof.CmacTripleDes.AArch64.ipG12 (by simp) p hp, VG.Proof.CmacTripleDes.AArch64.getLsbD_spreadW _ hp, VG.Proof.CmacTripleDes.AArch64.ipG12]
    cases hx : xBit p
    · simp
    · have hs := VG.Proof.CmacTripleDes.AArch64.ipSrc_lt ((xSrc p + 32 - rot) % 32) (by omega)
      simp only [ite_true, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs,
        Bool.true_and, split, BitVec.getLsbD_setWidth, decide_eq_true hj]
      rw [getLsbD_permute _ _ (by decide) (show (xSrc p + 32 - rot) % 32 < 64 by omega)]
      rfl

theorem spreadW_xPos (w : BitVec 32) {k : Nat} (hk : k < 32) :
    (VG.Proof.CmacTripleDes.AArch64.spreadW w).getLsbD (xPos ((k + rot) % 32)) = w.getLsbD k := by
  obtain ⟨h64, hx, hs⟩ := VG.Proof.CmacTripleDes.AArch64.xPos_facts ((k + rot) % 32) (by omega)
  rw [VG.Proof.CmacTripleDes.AArch64.getLsbD_spreadW _ h64, hx, hs, Bool.true_and]
  congr 1; simp only [rot]; omega

theorem fp_ok (s : VG.AArch64.State) {l r : BitVec 32} (hl : s.gpr .x11 = VG.Proof.CmacTripleDes.AArch64.spreadW l) (hr : s.gpr .x12 = VG.Proof.CmacTripleDes.AArch64.spreadW r) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      s'.gpr .x5 = Spec.TripleDes.permute Spec.TripleDes.fp (r ++ l) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ VG.Proof.CmacTripleDes.AArch64.blockKept, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.v = s.v ∧ (∀ p ∈ VG.Proof.CmacTripleDes.AArch64.maskConsts, s'.gpr p.1 = s.gpr p.1) := by
  let W : Nat → BitVec 64 := fun i => if i = 0 then s.gpr .x12 else s.gpr .x11
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.AArch64.fp_check (VG.Proof.CmacTripleDes.AArch64.oCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.AArch64.oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, fun r hr => hoth r (List.all_eq_true.mp VG.Proof.CmacTripleDes.AArch64.fp_kept r hr), VG.Proof.CmacTripleDes.AArch64.frame_oCfg hfr,
    runBlock_v VG.Proof.CmacTripleDes.AArch64.fp_v hs', fun p hp => hoth p.1 (List.all_eq_true.mp VG.Proof.CmacTripleDes.AArch64.fp_masks p hp)⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hs := VG.Proof.CmacTripleDes.AArch64.fpSrc_lt j hj
  rw [hout .x5 VG.Proof.CmacTripleDes.AArch64.fpG (by simp) j hj, getLsbD_permute _ _ (by decide) hj, BitVec.getLsbD_append,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl, VG.Proof.CmacTripleDes.AArch64.fpG]
  by_cases h32 : 32 ≤ fpSrc j
  · obtain ⟨h64, -, -⟩ := VG.Proof.CmacTripleDes.AArch64.xPos_facts ((fpSrc j - 32 + rot) % 32) (by omega)
    rw [ite_eq_left h32, ite_eq_right (by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.div_eq_of_lt h64,
      Nat.mod_eq_of_lt h64, W, ite_true, hr]
    exact VG.Proof.CmacTripleDes.AArch64.spreadW_xPos r (by omega)
  · obtain ⟨h64, -, -⟩ := VG.Proof.CmacTripleDes.AArch64.xPos_facts ((fpSrc j + rot) % 32) (by omega)
    rw [ite_eq_right h32, ite_eq_left (by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      show (64 + xPos ((fpSrc j + rot) % 32)) / 64 = 1 by omega,
      show (64 + xPos ((fpSrc j + rot) % 32)) % 64 = xPos ((fpSrc j + rot) % 32) by omega, W,
      show (1 : Nat) ≠ 0 by decide, ite_false, hl]
    exact VG.Proof.CmacTripleDes.AArch64.spreadW_xPos l (by omega)

/-! ## The setup -/

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : VG.Proof.CmacTripleDes.AArch64.kpos p j < 48 := by
  simp only [VG.Proof.CmacTripleDes.AArch64.kpos]; split <;> omega

/-- Before pass `p`, from the block `x`. -/
structure OInv (s₀ : VG.AArch64.State) (x : BitVec 64) (p : Nat) (s : VG.AArch64.State) : Prop where
  same : VG.Proof.CmacTripleDes.AArch64.Same s₀ s
  x14 : s.gpr .x14 = s₀.gpr .x14
  x10 : s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.AArch64.kpos p 0)
  consts : VG.Proof.CmacTripleDes.AArch64.Consts s
  masks : VG.Proof.CmacTripleDes.AArch64.Masks s
  keys : VG.Proof.CmacTripleDes.AArch64.Keys s₀ s.mem 48
  l : s.gpr .x11 = VG.Proof.CmacTripleDes.AArch64.spreadW (passes (VG.Proof.CmacTripleDes.AArch64.sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))).1
  r : s.gpr .x12 = VG.Proof.CmacTripleDes.AArch64.spreadW (passes (VG.Proof.CmacTripleDes.AArch64.sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))).2

theorem quarterConsts_ok (s : VG.AArch64.State) :
    ∃ s', runBlock isa quarterConsts s = some s' ∧ s'.v .v4 = bc 64 ∧ s'.v .v5 = bc 128 ∧
      s'.v .v6 = bc 192 ∧ (∀ w, w ≠ .v4 → w ≠ .v5 → w ≠ .v6 → s'.v w = s.v w) ∧
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine ⟨_, rfl, ?_, ?_, ?_, fun w h4 h5 h6 => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v6), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v5),
      v_setV_self, gpr_write_self, v_write, BitVec.setWidth_eq]
    rfl
  · simp only [v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v6), v_setV_self, gpr_write_self,
      v_write, BitVec.setWidth_eq]
    rfl
  · simp only [v_setV_self, gpr_write_self, BitVec.setWidth_eq]
    rfl
  · simp only [v_setV_of_ne _ _ h6, v_setV_of_ne _ _ h5, v_setV_of_ne _ _ h4, v_write]
  · simp only [gpr_setV, gpr_write_of_ne _ _ _ hr]

theorem maskSet_check :
    VG.AArch64.Straight.check (lanes 64 7) VG.Proof.CmacTripleDes.AArch64.oCfg (linExt 2) maskSet (linEnv [])
      (fun e => maskConsts.all fun p => e.cst p.1 == some p.2) = true := by
  lit_decide

/-- The registers the masks' setup keeps. -/
def maskKept : List Reg := [.x1, .x2, .x3, .x4, .x5, .x14, .x15]

theorem maskSet_keeps : maskKept.all (fun r => maskSet.all fun i => dstOf i != some r) = true := by
  lit_decide

theorem maskSet_v : maskSet.all (fun i => vdstOf i == none) = true := by lit_decide

theorem maskSet_ok (s : VG.AArch64.State) :
    ∃ s', runBlock isa maskSet s = some s' ∧ VG.Proof.CmacTripleDes.AArch64.Masks s' ∧ (∀ r ∈ VG.Proof.CmacTripleDes.AArch64.maskKept, s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.CmacTripleDes.AArch64.maskSet_check
  have hrel : Rel (LaneRel 7 0) VG.Proof.CmacTripleDes.AArch64.oCfg (linExt 2) (linEnv []) s :=
    ⟨fun r a h => (by simp [linEnv] at h), fun _ _ _ h => (by cases h),
      fun j _ hj _ => absurd hj (by simp [VG.Proof.CmacTripleDes.AArch64.oCfg]), fun _ _ h => (by cases h)⟩
  obtain ⟨s', hs', p⟩ := run lanes_sound (VG.Proof.CmacTripleDes.AArch64.oCfg_ok s) hrel he
  refine ⟨s', hs', fun r v hp => p.rel.cst r v ?_, fun r hr => p.other r fun h => ?_,
    runBlock_v VG.Proof.CmacTripleDes.AArch64.maskSet_v hs', VG.Proof.CmacTripleDes.AArch64.frame_oCfg p.frame, p.rd, p.wr, p.sp⟩
  · have := List.all_eq_true.mp hpost (r, v) hp
    simpa using this
  · rw [List.all_eq_true.mp VG.Proof.CmacTripleDes.AArch64.maskSet_keeps r hr] at h; cases h

/-- After the setup shared by the blocks of one call: the tables, constants,
masks and spread keys, and the block `x5` as it was. -/
structure TInv (s₀ s : VG.AArch64.State) : Prop where
  same : VG.Proof.CmacTripleDes.AArch64.Same s₀ s
  x5 : s.gpr .x5 = s₀.gpr .x5
  x14 : s.gpr .x14 = s₀.gpr .x14
  consts : VG.Proof.CmacTripleDes.AArch64.Consts s
  masks : VG.Proof.CmacTripleDes.AArch64.Masks s
  keys : VG.Proof.CmacTripleDes.AArch64.Keys s₀ s.mem 48

theorem tables_eq : tables = loadTable sTable ++ (quarterConsts ++ maskSet) := by
  simp only [tables, List.append_assoc]

theorem tables_ok {s₀ : VG.AArch64.State} {s : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.SInv s₀ 24 s) :
    WP isa (.block tables) s (VG.Proof.CmacTripleDes.AArch64.TInv s₀) := by
  rw [VG.Proof.CmacTripleDes.AArch64.tables_eq, WP.block_append_iff]
  refine WP.mono (loadTable_ok s sTable) fun a ⟨atab, av, ag, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  obtain ⟨b₀, hb, b4, b5, b6, bv₀, bg₀, bm₀, brd₀, bwr₀, bsp₀⟩ := VG.Proof.CmacTripleDes.AArch64.quarterConsts_ok a
  refine WP.of_runBlock ⟨b₀, hb, ?_⟩
  obtain ⟨b, hbm, bmask, bk, bvv, bm₁, brd₁, bwr₁, bsp₁⟩ := VG.Proof.CmacTripleDes.AArch64.maskSet_ok b₀
  refine WP.of_runBlock ⟨b, hbm, ?_⟩
  have bv : ∀ w, w ≠ .v4 → w ≠ .v5 → w ≠ .v6 → b.v w = a.v w := fun w h4 h5 h6 => by
    rw [bvv]; exact bv₀ w h4 h5 h6
  have g : ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.maskKept, r ≠ .x6 → r ≠ .x7 → b.gpr r = s.gpr r := fun r hr h6 h7 => by
    rw [bk r hr, bg₀ r h6, ag r h6 h7]
  have bm : b.mem = s.mem := by rw [bm₁, bm₀, am]
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨fun k hk => ?_, ?_, ?_, ?_⟩, bmask, ?_⟩
  · rw [g _ (by simp [VG.Proof.CmacTripleDes.AArch64.maskKept]) (by decide) (by decide), h.same.x15]
  · have hm : r ∈ VG.Proof.CmacTripleDes.AArch64.maskKept ∧ r ≠ .x6 ∧ r ≠ .x7 := by
      simp only [VG.Proof.CmacTripleDes.AArch64.outer, VG.Proof.CmacTripleDes.AArch64.maskKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [g r hm.1 hm.2.1 hm.2.2, h.same.keep r hr]
  · rw [bsp₁, bsp₀, asp, h.same.sp]
  · rw [brd₁, brd₀, ard, h.same.rd]
  · rw [bwr₁, bwr₀, awr, h.same.wr]
  · rw [bm]; exact h.same.frame
  · rw [g _ (by simp [VG.Proof.CmacTripleDes.AArch64.maskKept]) (by decide) (by decide), h.x5]
  · rw [g _ (by simp [VG.Proof.CmacTripleDes.AArch64.maskKept]) (by decide) (by decide), h.x14]
  · rw [tbyte_congr' (fun t ht => ?_) k hk, atab k hk]
    obtain ⟨-, -, -, -, h4, h5, h6, -⟩ := treg_ne8 t ht
    exact bv _ h4 h5 h6
  · rw [bvv]; exact b4
  · rw [bvv]; exact b5
  · rw [bvv]; exact b6
  · rw [bm]; exact h.keys

/-- `IP`, and `x10` to the first spread key: before the first pass. -/
theorem encStart_ok {s₀ : VG.AArch64.State} {s : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.TInv s₀ s) :
    WP isa (.block (ipCode ++ ([mov .x10 .x15] : List Instr))) s (VG.Proof.CmacTripleDes.AArch64.OInv s₀ (s₀.gpr .x5) 0) := by
  rw [WP.block_append_iff]
  obtain ⟨c, hc, c11, c12, crd, cwr, csp, ck, cm, cv, cmask⟩ := VG.Proof.CmacTripleDes.AArch64.ip_ok s
  refine WP.of_runBlock ⟨c, hc, ?_⟩
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_nil], ?_⟩
  have x15c : c.gpr .x15 = s₀.gpr .x15 := by rw [ck .x15 (by simp [VG.Proof.CmacTripleDes.AArch64.blockKept]), h.same.x15]
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.consts.congr (fun w _ _ _ _ => by rw [v_write, cv]),
    ?_, ?_, ?_, ?_⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), x15c]
  · have hk : r ∈ VG.Proof.CmacTripleDes.AArch64.blockKept ∧ r ≠ .x10 := by
      simp only [VG.Proof.CmacTripleDes.AArch64.outer, VG.Proof.CmacTripleDes.AArch64.blockKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [gpr_write_of_ne _ _ _ hk.2, ck r hk.1, h.same.keep r hr]
  · rw [sp_write, csp, h.same.sp]
  · rw [rd_write, crd, h.same.rd]
  · rw [wr_write, cwr, h.same.wr]
  · rw [mem_write, cm]; exact h.same.frame
  · rw [gpr_write_of_ne _ _ _ (by decide), ck .x14 (by simp [VG.Proof.CmacTripleDes.AArch64.blockKept]), h.x14]
  · rw [gpr_write_self, BitVec.setWidth_eq, x15c]
    simp [VG.Proof.CmacTripleDes.AArch64.kpos]
  · exact h.masks.congr fun p hp => by
      rw [gpr_write_of_ne _ _ _ (VG.Proof.CmacTripleDes.AArch64.maskRegs_ne p hp).2.1, cmask p hp]
  · rw [mem_write, cm]
    exact h.keys
  · rw [gpr_write_of_ne _ _ _ (by decide), c11, h.x5]
    rfl
  · rw [gpr_write_of_ne _ _ _ (by decide), c12, h.x5]
    rfl

/-! ## The passes -/

/-- After `j` pairs of rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : VG.AArch64.State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : VG.AArch64.State) : Prop where
  same : VG.Proof.CmacTripleDes.AArch64.Same s₀ s
  x14 : s.gpr .x14 = s₀.gpr .x14
  x10 : s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.AArch64.kpos p (2 * j))
  x16 : s.gpr .x16 = BitVec.ofNat 64 (8 - j)
  consts : VG.Proof.CmacTripleDes.AArch64.Consts s
  masks : VG.Proof.CmacTripleDes.AArch64.Masks s
  keys : VG.Proof.CmacTripleDes.AArch64.Keys s₀ s.mem 48
  l : s.gpr .x11 = VG.Proof.CmacTripleDes.AArch64.spreadW (VG.Proof.CmacTripleDes.rounds (passKeys (VG.Proof.CmacTripleDes.AArch64.sch s₀) p) (2 * j) lr).1
  r : s.gpr .x12 = VG.Proof.CmacTripleDes.AArch64.spreadW (VG.Proof.CmacTripleDes.rounds (passKeys (VG.Proof.CmacTripleDes.AArch64.sch s₀) p) (2 * j) lr).2

/-- The pass moves down the keys. -/
def downOf (p : Nat) : Bool := p % 2 == 1

theorem kpos_step (a : Addr) {p i : Nat} (hp : p < 3) (hi : i < 16) :
    (if VG.Proof.CmacTripleDes.AArch64.downOf p then a + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.AArch64.kpos p i) - 8 else a + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.AArch64.kpos p i) + 8) =
      a + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.AArch64.kpos p (i + 1)) := by
  simp only [VG.Proof.CmacTripleDes.AArch64.downOf, VG.Proof.CmacTripleDes.AArch64.kpos]
  by_cases h : p % 2 = 1
  · simp only [h, beq_self_eq_true, ite_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp only [h, ite_false, show (p % 2 == 1) = false by simp [h], Bool.false_eq_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem passKeys_at (s₀ : VG.AArch64.State) {p j : Nat} (hj : j < 16) :
    passKeys (VG.Proof.CmacTripleDes.AArch64.sch s₀) p j = ((VG.Proof.CmacTripleDes.AArch64.sch s₀).getD (VG.Proof.CmacTripleDes.AArch64.kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, VG.Proof.CmacTripleDes.AArch64.kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega]
  · rw [ite_eq_right h, ite_eq_right h]

theorem outer_ne {r : Reg} (h : r ∈ VG.Proof.CmacTripleDes.AArch64.outer) :
    r ≠ .x5 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x16 := by
  simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem pairBody_eq (down : Bool) :
    (round .x11 .x12 down ++ round .x12 .x11 down ++ ([.subImm .x .x16 .x16 1] : List Instr)) =
      round .x11 .x12 down ++ (round .x12 .x11 down ++ ([.subImm .x .x16 .x16 1] : List Instr)) := by
  simp only [List.append_assoc]

/-- Two rounds of pass `p`. -/
theorem pairStep_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 8) {s : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.PInv s₀ p lr j s) :
    WP isa (.block (round .x11 .x12 (VG.Proof.CmacTripleDes.AArch64.downOf p) ++ round .x12 .x11 (VG.Proof.CmacTripleDes.AArch64.downOf p) ++
      ([.subImm .x .x16 .x16 1] : List Instr))) s (VG.Proof.CmacTripleDes.AArch64.PInv s₀ p lr (j + 1)) := by
  rw [VG.Proof.CmacTripleDes.AArch64.pairBody_eq, WP.block_append_iff]
  have slot : ∀ {t : VG.AArch64.State}, VG.Proof.CmacTripleDes.AArch64.Same s₀ t → ∀ i < 48,
      InRegions (t.rd ++ t.wr) (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro t ht i hi
    obtain ⟨R, hR, hc⟩ := hp.slot ht (d := 8 * i) (n := 8) (by omega)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have k0 := VG.Proof.CmacTripleDes.AArch64.kpos_lt hp3 (show 2 * j < 16 by omega)
  have k1 := VG.Proof.CmacTripleDes.AArch64.kpos_lt hp3 (show 2 * j + 1 < 16 by omega)
  obtain ⟨s₁, h₁, a₁, x10₁, g₁, c₁, mk₁, m₁, rd₁, wr₁, sp₁⟩ := VG.Proof.CmacTripleDes.AArch64.round_ok (Or.inl ⟨rfl, rfl⟩) (VG.Proof.CmacTripleDes.AArch64.downOf p)
    h.consts h.masks (by rw [h.x10]; exact slot h.same _ k0) h.l h.r
    (by rw [h.x10]; exact h.keys _ k0)
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  rw [WP.block_append_iff]
  have same₁ : VG.Proof.CmacTripleDes.AArch64.Same s₀ s₁ := ⟨by rw [g₁ .x15 (by simp), h.same.x15],
    fun r hr => by rw [g₁ r (by simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> simp), h.same.keep r hr],
    by rw [sp₁, h.same.sp], by rw [rd₁, h.same.rd], by rw [wr₁, h.same.wr], by rw [m₁]; exact h.same.frame⟩
  have x10₁' : s₁.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.AArch64.kpos p (2 * j + 1)) := by
    rw [x10₁, h.x10, VG.Proof.CmacTripleDes.AArch64.kpos_step _ hp3 (by omega)]
  obtain ⟨s₂, h₂, a₂, x10₂, g₂, c₂, mk₂, m₂, rd₂, wr₂, sp₂⟩ := VG.Proof.CmacTripleDes.AArch64.round_ok (Or.inr ⟨rfl, rfl⟩) (VG.Proof.CmacTripleDes.AArch64.downOf p)
    c₁ mk₁ (by rw [x10₁']; exact slot same₁ _ k1) (by rw [g₁ .x12 (by simp), h.r]) a₁
    (by rw [x10₁', m₁]; exact h.keys _ k1)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have hr₁ := rounds_succ (passKeys (VG.Proof.CmacTripleDes.AArch64.sch s₀) p) (2 * j) lr
  have hr₂ := rounds_succ (passKeys (VG.Proof.CmacTripleDes.AArch64.sch s₀) p) (2 * j + 1) lr
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x15 (by simp), same₁.x15]
  · rw [gpr_write_of_ne _ _ _ (VG.Proof.CmacTripleDes.AArch64.outer_ne hr).2.2.2.2, g₂ r (by
      simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), same₁.keep r hr]
  · rw [sp_write, sp₂, same₁.sp]
  · rw [rd_write, rd₂, same₁.rd]
  · rw [wr_write, wr₂, same₁.wr]
  · rw [mem_write, m₂]; exact same₁.frame
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x14 (by simp), g₁ .x14 (by simp), h.x14]
  · rw [gpr_write_of_ne _ _ _ (by decide), x10₂, x10₁', VG.Proof.CmacTripleDes.AArch64.kpos_step _ hp3 (by omega),
      show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
  · rw [gpr_write_self, State.read, BitVec.setWidth_eq, BitVec.setWidth_eq, g₂ .x16 (by simp),
      g₁ .x16 (by simp), h.x16]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Size.bits]
    omega
  · exact c₂.congr fun _ _ _ _ _ => rfl
  · exact mk₂.congr fun p hp => gpr_write_of_ne _ _ _ (VG.Proof.CmacTripleDes.AArch64.maskRegs_ne p hp).2.2.2.2.1
  · rw [mem_write, m₂, m₁]; exact h.keys
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x11 (by simp), a₁, show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      hr₂, hr₁, VG.Proof.CmacTripleDes.AArch64.passKeys_at s₀ (show 2 * j < 16 by omega)]
  · rw [gpr_write_of_ne _ _ _ (by decide), a₂, show 2 * (j + 1) = 2 * j + 1 + 1 by omega, hr₂, hr₁,
      VG.Proof.CmacTripleDes.AArch64.passKeys_at s₀ (show 2 * j < 16 by omega), VG.Proof.CmacTripleDes.AArch64.passKeys_at s₀ (show 2 * j + 1 < 16 by omega)]

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.Same s₀ s) (h14 : s.gpr .x14 = s₀.gpr .x14)
    (h10 : s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.AArch64.kpos p 0)) (hc : VG.Proof.CmacTripleDes.AArch64.Consts s) (hm : VG.Proof.CmacTripleDes.AArch64.Masks s)
    (hk : VG.Proof.CmacTripleDes.AArch64.Keys s₀ s.mem 48) (hl : s.gpr .x11 = VG.Proof.CmacTripleDes.AArch64.spreadW lr.1) (hr : s.gpr .x12 = VG.Proof.CmacTripleDes.AArch64.spreadW lr.2) :
    WP isa (pass (VG.Proof.CmacTripleDes.AArch64.downOf p)) s (VG.Proof.CmacTripleDes.AArch64.PInv s₀ p lr 8) := by
  refine WP.seq (WP.of_runBlock ⟨_, by rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_movz_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have g : ∀ r, r ≠ .x16 → (s.write .x .x16 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))).gpr r = s.gpr r :=
    fun r hr => gpr_write_of_ne _ _ _ hr
  have hI : VG.Proof.CmacTripleDes.AArch64.PInv s₀ p lr 0 (s.write .x .x16 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))) :=
    ⟨⟨by rw [g _ (by decide), h.x15], fun r hr => by rw [g _ (VG.Proof.CmacTripleDes.AArch64.outer_ne hr).2.2.2.2, h.keep r hr],
      h.sp, h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h14], by rw [g _ (by decide), h10],
      by rw [gpr_write_self]; decide, hc.congr fun _ _ _ _ _ => rfl,
      hm.congr fun p hp => g _ (VG.Proof.CmacTripleDes.AArch64.maskRegs_ne p hp).2.2.2.2.1, hk,
      by rw [g _ (by decide), hl]; rfl, by rw [g _ (by decide), hr]; rfl⟩
  refine WP.loop (M := isa)
    (body := .block (round .x11 .x12 (VG.Proof.CmacTripleDes.AArch64.downOf p) ++ round .x12 .x11 (VG.Proof.CmacTripleDes.AArch64.downOf p) ++ [.subImm .x .x16 .x16 1]))
    (c := .nonzero .x .x16) (Q := VG.Proof.CmacTripleDes.AArch64.PInv s₀ p lr 8)
    (fun (n : Nat) (t : VG.AArch64.State) => ∃ j, n = 8 - j ∧ j < 8 ∧ VG.Proof.CmacTripleDes.AArch64.PInv s₀ p lr j t) ?_ 8 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.pairStep_ok hp hp3 hj ht) fun t' h' => ?_
  have ev := VG.Proof.CmacTripleDes.AArch64.eval_nonzero (r := .x16) (x := 8 - (j + 1)) (by omega) h'.x16
  by_cases hz : j + 1 = 8
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega, 8 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

theorem passTail_ok (s : VG.AArch64.State) (d : Nat) (hd : d < 4096) :
    ∃ s', runBlock isa (passTail d) s = some s' ∧
      s'.gpr .x10 = s.gpr .x10 + BitVec.ofNat 64 d ∧ s'.gpr .x11 = s.gpr .x12 ∧
      s'.gpr .x12 = s.gpr .x11 ∧ (∀ r, r ≠ .x5 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x10 (s.read .x .x10 + BitVec.ofNat _ d)
  let s₂ := s₁.write .x .x5 (s₁.gpr .x11)
  let s₃ := s₂.write .x .x11 (s₂.gpr .x12)
  let s₄ := s₃.write .x .x12 (s₃.gpr .x5)
  refine ⟨s₄, by
    rw [passTail, runBlock_cons, exec_addImm_x hd, runStep_some, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some,
      runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_nil],
    ?_, ?_, ?_, fun r h5 h10 h11 h12 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [s₄, s₃, s₂, s₁, gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x12),
      gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x11), gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x5),
      gpr_write_self, State.read, BitVec.setWidth_eq]
  · simp only [s₄, s₃, gpr_write_of_ne _ _ _ (by decide : Reg.x11 ≠ .x12), gpr_write_self,
      BitVec.setWidth_eq, s₂, gpr_write_of_ne _ _ _ (by decide : Reg.x12 ≠ .x5), s₁,
      gpr_write_of_ne _ _ _ (by decide : Reg.x12 ≠ .x10)]
  · simp only [s₄, gpr_write_self, BitVec.setWidth_eq, s₃, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x11),
      s₂, s₁, gpr_write_of_ne _ _ _ (by decide : Reg.x11 ≠ .x10)]
  · simp only [s₄, s₃, s₂, s₁, gpr_write_of_ne _ _ _ h12, gpr_write_of_ne _ _ _ h11,
      gpr_write_of_ne _ _ _ h5, gpr_write_of_ne _ _ _ h10]

/-- One pass and the exchange after it (the first two passes). -/
theorem passStep_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {x : BitVec 64} {p : Nat} (hp2 : p < 2) {s : VG.AArch64.State}
    (h : VG.Proof.CmacTripleDes.AArch64.OInv s₀ x p s) :
    WP isa (.seq (pass (VG.Proof.CmacTripleDes.AArch64.downOf p)) (.block (passTail (if p = 0 then 120 else 136)))) s (VG.Proof.CmacTripleDes.AArch64.OInv s₀ x (p + 1)) := by
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.pass_ok hp (by omega) h.same h.x14 h.x10 h.consts h.masks h.keys h.l h.r) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t10, t11, t12, tk, tv, tsp, tm, trd, twr⟩ :=
    VG.Proof.CmacTripleDes.AArch64.passTail_ok s₁ (if p = 0 then 120 else 136) (by split <;> decide)
  refine WP.of_runBlock ⟨s₂, h₂, ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tk .x15 (by decide) (by decide) (by decide) (by decide), h₁.same.x15]
  · obtain ⟨a, b, c, d, -⟩ := VG.Proof.CmacTripleDes.AArch64.outer_ne hr
    rw [tk r a b c d, h₁.same.keep r hr]
  · rw [tsp, h₁.same.sp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [tk .x14 (by decide) (by decide) (by decide) (by decide), h₁.x14]
  · rw [t10, h₁.x10, Offset.add_add]
    congr 2
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> decide
  · exact h₁.consts.congr fun _ _ _ _ _ => by rw [tv]
  · exact h₁.masks.congr fun p hp => by
      obtain ⟨a, b, c, d, -⟩ := VG.Proof.CmacTripleDes.AArch64.maskRegs_ne p hp
      exact tk _ a b c d
  · rw [tm]; exact h₁.keys
  · rw [t11, h₁.r, passes, swap]
  · rw [t12, h₁.l, passes, swap]

/-- The setup the blocks of one call share, but for the saves. -/
theorem prepCore_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) :
    WP isa (.seq (.block spreadPre) (.seq (.loop (.block spreadBody) (.nonzero .x .x16))
      (.block tables))) s₀ (VG.Proof.CmacTripleDes.AArch64.TInv s₀) := by
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.spreadPre_ok s₀) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.spreadLoop_ok hp h₁) fun s₂ h₂ => ?_)
  exact VG.Proof.CmacTripleDes.AArch64.tables_ok h₂

/-- TDEA encryption of the block in `x5` (as a 64-bit integer) with the key
schedule at `x14` (spread at `x15`), into `x5`. -/
theorem enc_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) {s : VG.AArch64.State} (h : VG.Proof.CmacTripleDes.AArch64.TInv s₀ s) :
    WP isa enc s fun s' =>
      VG.Proof.CmacTripleDes.AArch64.Same s₀ s' ∧ s'.gpr .x14 = s₀.gpr .x14 ∧ s'.gpr .x5 = VG.Proof.CmacTripleDes.tdes (VG.Proof.CmacTripleDes.AArch64.sch s₀) (s₀.gpr .x5) ∧
      VG.Proof.CmacTripleDes.AArch64.Consts s' ∧ VG.Proof.CmacTripleDes.AArch64.Masks s' ∧ VG.Proof.CmacTripleDes.AArch64.Keys s₀ s'.mem 48 := by
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.encStart_ok h) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.passStep_ok hp (p := 0) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.passStep_ok hp (p := 1) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.pass_ok hp (p := 2) (by decide) h₅.same h₅.x14 h₅.x10 h₅.consts h₅.masks h₅.keys
    h₅.l h₅.r) fun s₆ h₆ => ?_)
  obtain ⟨s₇, h₇, x5₇, rd₇, wr₇, sp₇, k₇, m₇, v₇, mk₇⟩ := VG.Proof.CmacTripleDes.AArch64.fp_ok s₆ h₆.l h₆.r
  refine WP.of_runBlock ⟨s₇, h₇, ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    h₆.consts.congr (fun w _ _ _ _ => by rw [v₇]), h₆.masks.congr mk₇, by rw [m₇]; exact h₆.keys⟩⟩
  · rw [k₇ .x15 (by simp [VG.Proof.CmacTripleDes.AArch64.blockKept]), h₆.same.x15]
  · have hk : r ∈ VG.Proof.CmacTripleDes.AArch64.blockKept := by
      simp only [VG.Proof.CmacTripleDes.AArch64.outer, VG.Proof.CmacTripleDes.AArch64.blockKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [k₇ r hk, h₆.same.keep r hr]
  · rw [sp₇, h₆.same.sp]
  · rw [rd₇, h₆.same.rd]
  · rw [wr₇, h₆.same.wr]
  · rw [m₇]; exact h₆.same.frame
  · rw [k₇ .x14 (by simp [VG.Proof.CmacTripleDes.AArch64.blockKept]), h₆.x14]
  · rw [x5₇, tdes_eq]
    rfl

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

/-! ## Keeping the callee-saved registers -/

/-- The callee-saved mask registers' slots, after the spread round keys. -/
def saveSlots : List (Reg × Nat) := (List.range 9).map fun i => (savedReg i, 384 + 8 * i)

theorem save_eq : blockSave = Spill.saveCode .x15 VG.Proof.CmacTripleDes.AArch64.saveSlots := by decide

theorem restore_eq : blockRestore = Spill.restoreCode .x15 VG.Proof.CmacTripleDes.AArch64.saveSlots := by decide

theorem saveSlots_facts : (∀ p ∈ VG.Proof.CmacTripleDes.AArch64.saveSlots, 384 ≤ p.2 ∧ p.2 + 8 ≤ 384 + 72) ∧
    (∀ p ∈ VG.Proof.CmacTripleDes.AArch64.saveSlots, p.2 % 8 = 0 ∧ p.2 < 32768) ∧ Spill.Fits VG.Proof.CmacTripleDes.AArch64.saveSlots ∧
    Spill.Restorable .x15 VG.Proof.CmacTripleDes.AArch64.saveSlots ∧ .x15 ∉ saveSlots.map Prod.fst ∧ .x14 ∉ saveSlots.map Prod.fst ∧
    .x5 ∉ saveSlots.map Prod.fst ∧ (∀ r ∈ VG.Proof.CmacTripleDes.AArch64.outer, r ∉ saveSlots.map Prod.fst) := by
  decide

/-- The callee-saved registers the block writes. -/
def savedRegs : List Reg := (List.range 9).map savedReg

theorem mem_savedRegs {r : Reg} (h : r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs) : ∃ i < 9, r = savedReg i := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem mem_saveSlots {i : Nat} (hi : i < 9) : (savedReg i, 384 + 8 * i) ∈ VG.Proof.CmacTripleDes.AArch64.saveSlots :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- What the block keeps: `Same`, with the saves' slots too. -/
structure SameB (s₀ s : VG.AArch64.State) : Prop where
  x15 : s.gpr .x15 = s₀.gpr .x15
  keep : ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.outer, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .x15, 456⟩] s₀.mem s.mem

/-- After `prep`: the setup the blocks share, with the callee-saved
registers saved. -/
structure PrepPost (s₀ s : VG.AArch64.State) : Prop where
  same : VG.Proof.CmacTripleDes.AArch64.SameB s₀ s
  x5 : s.gpr .x5 = s₀.gpr .x5
  x14 : s.gpr .x14 = s₀.gpr .x14
  consts : VG.Proof.CmacTripleDes.AArch64.Consts s
  masks : VG.Proof.CmacTripleDes.AArch64.Masks s
  keys : VG.Proof.CmacTripleDes.AArch64.Keys s₀ s.mem 48
  slots : Spill.Saved (s₀.gpr .x15) s₀.gpr VG.Proof.CmacTripleDes.AArch64.saveSlots s.mem

theorem prep_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) : WP isa prep s₀ (VG.Proof.CmacTripleDes.AArch64.PrepPost s₀) := by
  obtain ⟨hl, ho, hf, -, -, -, -, -⟩ := VG.Proof.CmacTripleDes.AArch64.saveSlots_facts
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  have slotIn : ∀ p ∈ VG.Proof.CmacTripleDes.AArch64.saveSlots, X.Contains ((s₀.gpr .x15) + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [← hXb]; exact Offset.contains_base _ (by have := hl p hp'; omega) (by have := hl p hp'; omega)
  rw [prep, VG.Proof.CmacTripleDes.AArch64.save_eq]
  apply WP.seq
  refine WP.mono (Spill.save_wp ho fun p hp' => ⟨X, hX, slotIn p hp'⟩) fun s₁ st => ?_
  have saveF : Frame [⟨(s₀.gpr .x15) + BitVec.ofNat 64 384, 72⟩] s₀.mem s₁.mem := by
    rw [st.mem]; exact Spill.saveMem_frame hl (by decide) _ _ _
  have bp₁ : VG.Proof.CmacTripleDes.AArch64.BlockPre s₁ :=
    ⟨by rw [st.rd, st.wr, st.gpr]; exact hp.sched, by rw [st.wr, st.gpr]; exact hp.scr,
      by rw [st.gpr]; exact hp.disj⟩
  have sch₁ : VG.Proof.CmacTripleDes.AArch64.sch s₁ = VG.Proof.CmacTripleDes.AArch64.sch s₀ := by
    simp only [VG.Proof.CmacTripleDes.AArch64.sch, st.gpr]
    exact VG.Proof.CmacTripleDes.AArch64.scheduleAt_frame saveF fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact (hp.disj.sub_left (Offset.sub_base _ (by decide))).symm
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.prepCore_ok bp₁) fun s₂ h₂ => ?_
  have sv : Spill.Saved (s₀.gpr .x15) s₀.gpr VG.Proof.CmacTripleDes.AArch64.saveSlots s₂.mem := by
    have h := Spill.saveMem_saved hf s₀.mem (s₀.gpr .x15) s₀.gpr
    rw [← st.mem] at h
    refine h.frame_in hl h₂.same.frame fun r hr' => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    simp only [VG.Proof.CmacTripleDes.AArch64.xR, st.gpr]
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h₂.consts, h₂.masks, fun i hi => ?_, sv⟩
  · rw [h₂.same.x15, st.gpr]
  · rw [h₂.same.keep r hr, st.gpr]
  · rw [h₂.same.sp, st.sp]
  · rw [h₂.same.rd, st.rd]
  · rw [h₂.same.wr, st.wr]
  · refine (saveF.sub fun r hr' => ?_).trans (h₂.same.frame.sub fun r hr' => ?_)
    · simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_singleton_self _, by simp only [VG.Proof.CmacTripleDes.AArch64.xR, st.gpr]; exact Region.sub_prefix (by decide)⟩
  · rw [h₂.x5, st.gpr]
  · rw [h₂.x14, st.gpr]
  · have := h₂.keys i hi
    simp only [sch₁, st.gpr] at this
    exact this

/-- The callee-saved registers restored. -/
theorem restore_ok' {s₀ s : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) (h15 : s.gpr .x15 = s₀.gpr .x15)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hs : Spill.Saved (s₀.gpr .x15) s₀.gpr VG.Proof.CmacTripleDes.AArch64.saveSlots s.mem) :
    WP isa (.block blockRestore) s (Spill.Restored s₀.gpr VG.Proof.CmacTripleDes.AArch64.saveSlots s) := by
  obtain ⟨hl, ho, -, hr, -, -, -, -⟩ := VG.Proof.CmacTripleDes.AArch64.saveSlots_facts
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  have slotIn : ∀ p ∈ VG.Proof.CmacTripleDes.AArch64.saveSlots, X.Contains ((s₀.gpr .x15) + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [← hXb]; exact Offset.contains_base _ (by have := hl p hp'; omega) (by have := hl p hp'; omega)
  rw [VG.Proof.CmacTripleDes.AArch64.restore_eq]
  refine Spill.restore_wp h15 ho hr (fun p hp' => ?_) hs
  rw [hrd, hwr]
  exact ⟨X, List.mem_append_right _ hX, slotIn p hp'⟩

/-- TDEA encryption of the block in `x5` (as a 64-bit integer) with the key
schedule at `x14`, into `x5`. -/
theorem block_ok {s₀ : VG.AArch64.State} (hp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₀) :
    WP isa VG.Impl.CmacTripleDes.AArch64.block s₀ fun s =>
      VG.Proof.CmacTripleDes.AArch64.SameB s₀ s ∧ s.gpr .x14 = s₀.gpr .x14 ∧ s.gpr .x5 = VG.Proof.CmacTripleDes.tdes (VG.Proof.CmacTripleDes.AArch64.sch s₀) (s₀.gpr .x5) ∧
      ∀ i < 9, s.gpr (savedReg i) = s₀.gpr (savedReg i) := by
  obtain ⟨-, -, -, -, h15, h14, h5, hout⟩ := VG.Proof.CmacTripleDes.AArch64.saveSlots_facts
  rw [VG.Impl.CmacTripleDes.AArch64.block]
  apply WP.seq
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.prep_ok hp) fun s₁ h₁ => ?_
  have bp₁ : VG.Proof.CmacTripleDes.AArch64.BlockPre s₁ :=
    ⟨by rw [h₁.same.rd, h₁.same.wr, h₁.x14]; exact hp.sched,
      by rw [h₁.same.wr, h₁.same.x15]; exact hp.scr, by rw [h₁.x14, h₁.same.x15]; exact hp.disj⟩
  have sch₁ : VG.Proof.CmacTripleDes.AArch64.sch s₁ = VG.Proof.CmacTripleDes.AArch64.sch s₀ := by
    simp only [VG.Proof.CmacTripleDes.AArch64.sch, h₁.x14]
    exact VG.Proof.CmacTripleDes.AArch64.scheduleAt_frame h₁.same.frame fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hp.disj.symm
  have t₁ : VG.Proof.CmacTripleDes.AArch64.TInv s₁ s₁ := ⟨Same.refl _, rfl, rfl, h₁.consts, h₁.masks, fun i hi => by
    rw [h₁.same.x15, sch₁]; exact h₁.keys i hi⟩
  apply WP.seq
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.enc_ok bp₁ t₁) fun s₂ ⟨same₂, x14₂, x5₂, _, _, _⟩ => ?_
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.restore_ok' hp (by rw [same₂.x15, h₁.same.x15]) (by rw [same₂.rd, h₁.same.rd])
    (by rw [same₂.wr, h₁.same.wr]) (h₁.slots.frame_in (lo := 384) (n := 72)
      (saveSlots_facts.1) same₂.frame fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        simp only [VG.Proof.CmacTripleDes.AArch64.xR, h₁.same.x15]
        exact Offset.disjoint_base _ (by decide) (by decide))) fun s₃ h₃ => ?_
  refine ⟨⟨?_, fun r hr' => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun i hi => ?_⟩
  · rw [h₃.other _ h15, same₂.x15, h₁.same.x15]
  · rw [h₃.other _ (hout r hr'), same₂.keep r hr', h₁.same.keep r hr']
  · rw [h₃.sp, same₂.sp, h₁.same.sp]
  · rw [h₃.rd, same₂.rd, h₁.same.rd]
  · rw [h₃.wr, same₂.wr, h₁.same.wr]
  · rw [h₃.mem]
    refine h₁.same.frame.trans (same₂.frame.sub fun r hr' => ?_)
    simp only [List.mem_singleton] at hr'; subst hr'
    exact ⟨_, List.mem_singleton_self _, by simp only [VG.Proof.CmacTripleDes.AArch64.xR, h₁.same.x15]; exact Region.sub_prefix (by decide)⟩
  · rw [h₃.other _ h14, x14₂, h₁.x14]
  · rw [h₃.other _ h5, x5₂, sch₁, h₁.x5]
  · exact h₃.gpr_of (.inl (List.mem_map.mpr ⟨_, VG.Proof.CmacTripleDes.AArch64.mem_saveSlots hi, rfl⟩))

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.KeysLit`. -/
section

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

namespace VG

materialize_value Impl.CmacTripleDes.AArch64.roundKeys

theorem Proof.CmacTripleDes.AArch64.roundKeys_eq :
    Impl.CmacTripleDes.AArch64.roundKeys = Impl.CmacTripleDes.AArch64.roundKeys.lit :=
  Impl.CmacTripleDes.AArch64.roundKeys.lit_eq

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Lit`. -/
section

/-! # TDEA-CMAC's AArch64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.CmacTripleDes.AArch64.init
materialize_code Impl.CmacTripleDes.AArch64.update
materialize_code Impl.CmacTripleDes.AArch64.finalize

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Contract`. -/
section

/-!
# TDEA-CMAC on AArch64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of
`Spec/Cmac/TripleDesContract.lean`, which imply these (`Verified.lean`). The
functions call nothing and use no stack: the return address stays in `x30`.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key = x0, key_len = x1, out = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let out : Region := ⟨s.gpr .x2, 400⟩
    let scr : Region := ⟨s.gpr .x3, 640⟩
    s.rd = [key] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 400 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 640 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .x1).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (s.gpr .x2) = k ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .x2 + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_update(schedule = x0, state = x1, data = x2, n = x3, scratch = x4)`. -/
def updateAArch64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 384⟩
    let state : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let scr : Region := ⟨s.gpr .x4, 640⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + 640 ≤ 2 ^ 64
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cmac.chain (VG.Proof.CmacTripleDes.AArch64.ciphAt s.mem (s.gpr .x0)) (Spec.Aes.bytesAt s.mem (s.gpr .x1) 8)
        (Spec.Cmac.blocksAt s.mem (s.gpr .x2) 8 (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_finalize(key = x0, state = x1, last = x2, last_len = x3, scratch = x4)`. -/
def finalizeAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 400⟩
    let state : Region := ⟨s.gpr .x1, 8⟩
    let last : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scr : Region := ⟨s.gpr .x4, 640⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .x0).toNat + 400 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 640 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat ≤ 8
  post s s' :=
    let ciph := VG.Proof.CmacTripleDes.AArch64.ciphAt s.mem (s.gpr .x0)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (s.gpr .x0 + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (s.gpr .x3).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .x1) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.CT`. -/
section

/-!
# TDEA-CMAC on AArch64: constant time

The taint analysis (`Framework/AArch64/Taint.lean`) checks that only the
arguments, which are public, decide branches and addresses: the functions keep
their pointers and counts in registers.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64

theorem init_ct : ConstantTime isa initAArch64.pre initAArch64.pub Impl.CmacTripleDes.AArch64.init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem update_ct : ConstantTime isa updateAArch64.pre updateAArch64.pub Impl.CmacTripleDes.AArch64.update := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem finalize_ct :
    ConstantTime isa finalizeAArch64.pre finalizeAArch64.pub Impl.CmacTripleDes.AArch64.finalize := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update`. -/
section

/-!
# TDEA-CMAC on AArch64: `vg_cmac_triple_des_update`

The invariant after `k` blocks (`LInv`): `x2` points to the next block, `x3`
holds the blocks left, only the state and the block's slots have changed, and
the state is the chaining value after the first `k` blocks.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes VG.Proof.Cmac

theorem rev64_eq (x : BitVec 64) : rev64 x = byteRev64 x := rfl

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

theorem add_ofNat_zero (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .x0
abbrev St : Addr := s₀.gpr .x1
abbrev Dp : Addr := s₀.gpr .x2
abbrev N : Nat := (s₀.gpr .x3).toNat
abbrev S : Addr := s₀.gpr .x4

abbrev schR : Region := ⟨VG.Proof.CmacTripleDes.AArch64.W s₀, 384⟩
abbrev stR : Region := ⟨VG.Proof.CmacTripleDes.AArch64.St s₀, 8⟩
abbrev dataR : Region := ⟨VG.Proof.CmacTripleDes.AArch64.Dp s₀, 8 * VG.Proof.CmacTripleDes.AArch64.N s₀⟩
abbrev scrR : Region := ⟨VG.Proof.CmacTripleDes.AArch64.S s₀, 640⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := VG.Proof.CmacTripleDes.AArch64.ciphAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.W s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.Dp s₀) 8 (VG.Proof.CmacTripleDes.AArch64.N s₀)

/-- What changes. -/
abbrev chg : List Region := [VG.Proof.CmacTripleDes.AArch64.stR s₀, ⟨VG.Proof.CmacTripleDes.AArch64.S s₀, 456⟩]

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacTripleDes.AArch64.schR s₀, VG.Proof.CmacTripleDes.AArch64.dataR s₀]
  wr : s₀.wr = [VG.Proof.CmacTripleDes.AArch64.stR s₀, VG.Proof.CmacTripleDes.AArch64.scrR s₀]
  sch_st : (VG.Proof.CmacTripleDes.AArch64.schR s₀).Disjoint (VG.Proof.CmacTripleDes.AArch64.stR s₀)
  sch_scr : (VG.Proof.CmacTripleDes.AArch64.schR s₀).Disjoint (VG.Proof.CmacTripleDes.AArch64.scrR s₀)
  data_st : (VG.Proof.CmacTripleDes.AArch64.dataR s₀).Disjoint (VG.Proof.CmacTripleDes.AArch64.stR s₀)
  data_scr : (VG.Proof.CmacTripleDes.AArch64.dataR s₀).Disjoint (VG.Proof.CmacTripleDes.AArch64.scrR s₀)
  st_scr : (VG.Proof.CmacTripleDes.AArch64.stR s₀).Disjoint (VG.Proof.CmacTripleDes.AArch64.scrR s₀)
  st_wrap : (VG.Proof.CmacTripleDes.AArch64.St s₀).toNat + 8 ≤ 2 ^ 64
  data_wrap : (VG.Proof.CmacTripleDes.AArch64.Dp s₀).toNat + 8 * VG.Proof.CmacTripleDes.AArch64.N s₀ ≤ 2 ^ 64
  scr_wrap : (VG.Proof.CmacTripleDes.AArch64.S s₀).toNat + 640 ≤ 2 ^ 64

theorem UPre.of {s₀ : State} (h : updateAArch64.pre s₀) : VG.Proof.CmacTripleDes.AArch64.UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = VG.Proof.CmacTripleDes.AArch64.W s₀
  x15 : s.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.S s₀
  x1 : s.gpr .x1 = VG.Proof.CmacTripleDes.AArch64.St s₀
  x2 : s.gpr .x2 = VG.Proof.CmacTripleDes.AArch64.Dp s₀ + BitVec.ofNat 64 (8 * k)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (VG.Proof.CmacTripleDes.AArch64.N s₀ - k)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (VG.Proof.CmacTripleDes.AArch64.chg s₀) s₀.mem s.mem
  consts : VG.Proof.CmacTripleDes.AArch64.Consts s
  masks : VG.Proof.CmacTripleDes.AArch64.Masks s
  keys : ∀ i < 48, s.mem.readW (VG.Proof.CmacTripleDes.AArch64.S s₀ + BitVec.ofNat 64 (8 * i)) 64 =
    VG.Proof.CmacTripleDes.AArch64.spread ((Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.W s₀)).getD i 0)
  slots : Spill.Saved (VG.Proof.CmacTripleDes.AArch64.S s₀) s₀.gpr VG.Proof.CmacTripleDes.AArch64.saveSlots s.mem
  state : Spec.Aes.bytesAt s.mem (VG.Proof.CmacTripleDes.AArch64.St s₀) 8 =
    Spec.Cmac.chain (VG.Proof.CmacTripleDes.AArch64.ciph s₀) (Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.St s₀) 8) ((VG.Proof.CmacTripleDes.AArch64.blks s₀).take k)

/-! ## The blocks of straight-line code -/

theorem chainIn_ok (s : State) {P Q : Addr} (hp : s.gpr .x1 = P) (hq : s.gpr .x2 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rq : InRegions (s.rd ++ s.wr) Q 8) :
    ∃ s', runBlock isa chainIn s = some s' ∧
      s'.gpr .x5 = byteRev64 (s.mem.readW P 64 ^^^ s.mem.readW Q 64) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have rp' : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8 := by rw [VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero, hp]; exact rp
  let s₁ := s.write .x .x5 (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 0) 64)
  have rq' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 0) 8 := by
    rw [VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero, gpr_write_of_ne _ _ _ (by decide), hq]; exact rq
  refine ⟨_, by
    rw [chainIn, runBlock_cons, exec_ldr_x (by decide) rp', runStep_some, runBlock_cons, exec_ldr_x (by decide) rq',
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_rev, runStep_some, runBlock_nil],
    ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [reduceCtorEq, ↓reduceIte, s₁, State.read, gpr_write, mem_write,
      BitVec.setWidth_eq, VG.Proof.CmacTripleDes.AArch64.rev64_eq, VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero, hp, hq]
  · simp [s₁, gpr_write, h₁, h₂]

theorem chainOut_ok (s : State) {P : Addr} (hp : s.gpr .x1 = P) (wp : InRegions s.wr P 8) :
    ∃ s', runBlock isa chainOut s = some s' ∧
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 8 ∧ s'.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ∉ [Reg.x2, .x3, .x5] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (byteRev64 (s.gpr .x5)) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x5 (rev64 (s.read .x .x5))
  have wp' : InRegions s₁.wr (s₁.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    rw [VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero, gpr_write_of_ne _ _ _ (by decide), hp]; exact wp
  refine ⟨_, by
    rw [chainOut, runBlock_cons, exec_rev, runStep_some, runBlock_cons, exec_str_x (by decide) wp',
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
  · simp [s₁, gpr_write, State.read]
  · simp [s₁, gpr_write, State.read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s₁, gpr_write, hr.1, hr.2.1, hr.2.2]
  · simp only [reduceCtorEq, ↓reduceIte, s₁, mem_write, State.read, gpr_write,
      BitVec.setWidth_eq, VG.Proof.CmacTripleDes.AArch64.rev64_eq, hp, VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero]

theorem chainIn_v : chainIn.all (fun i => vdstOf i == none) = true := by decide
theorem chainOut_v : chainOut.all (fun i => vdstOf i == none) = true := by decide

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨VG.Proof.CmacTripleDes.AArch64.S s₀ + BitVec.ofNat 64 d, n⟩ (VG.Proof.CmacTripleDes.AArch64.scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < VG.Proof.CmacTripleDes.AArch64.N s₀) :
    Region.Sub ⟨VG.Proof.CmacTripleDes.AArch64.Dp s₀ + BitVec.ofNat 64 (8 * k), 8⟩ (VG.Proof.CmacTripleDes.AArch64.dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.sched {hp : VG.Proof.CmacTripleDes.AArch64.UPre s₀} {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.AArch64.chg s₀) s₀.mem m) :
    Spec.TripleDes.scheduleAt m (VG.Proof.CmacTripleDes.AArch64.W s₀) = Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.W s₀) :=
  VG.Proof.CmacTripleDes.AArch64.scheduleAt_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))

theorem UPre.data {hp : VG.Proof.CmacTripleDes.AArch64.UPre s₀} {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.AArch64.chg s₀) s₀.mem m) {k : Nat}
    (hk : k < VG.Proof.CmacTripleDes.AArch64.N s₀) :
    Spec.Aes.bytesAt m (VG.Proof.CmacTripleDes.AArch64.Dp s₀ + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.Dp s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.data_st.sub_left (UPre.data_sub hk)
    · exact (hp.data_scr.sub_right (Region.sub_prefix (by decide))).sub_left (UPre.data_sub hk))
    (by decide)

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {hp : VG.Proof.CmacTripleDes.AArch64.UPre s₀} {s : State} (h14 : s.gpr .x14 = VG.Proof.CmacTripleDes.AArch64.W s₀) (h15 : s.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : VG.Proof.CmacTripleDes.AArch64.BlockPre s where
  sched := ⟨VG.Proof.CmacTripleDes.AArch64.schR s₀, by rw [hrd, hwr, hp.rd]; simp, by rw [h14], Nat.le_refl _, by show 384 < 2 ^ 64; decide⟩
  scr := ⟨VG.Proof.CmacTripleDes.AArch64.scrR s₀, by rw [hwr, hp.wr]; simp, by rw [h15], by show 456 ≤ 640; decide, by show 640 < 2 ^ 64; decide⟩
  disj := by
    rw [h14, h15]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem x2_succ (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.AArch64.N s₀) :
    (VG.Proof.CmacTripleDes.AArch64.blks s₀).take (k + 1) =
      (VG.Proof.CmacTripleDes.AArch64.blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.Dp s₀ + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

theorem body_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.AArch64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.AArch64.N s₀) {s : State} (h : VG.Proof.CmacTripleDes.AArch64.LInv s₀ k s) :
    WP isa updBody s (VG.Proof.CmacTripleDes.AArch64.LInv s₀ (k + 1)) := by
  have hN : VG.Proof.CmacTripleDes.AArch64.N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have hdw := hp.data_wrap
  have sw := hp.scr_wrap
  have rdwr : s.rd ++ s.wr = [VG.Proof.CmacTripleDes.AArch64.schR s₀, VG.Proof.CmacTripleDes.AArch64.dataR s₀, VG.Proof.CmacTripleDes.AArch64.stR s₀, VG.Proof.CmacTripleDes.AArch64.scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₁, h₁, ax₁, k₁, sp₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.AArch64.chainIn_ok s (P := VG.Proof.CmacTripleDes.AArch64.St s₀)
    (Q := VG.Proof.CmacTripleDes.AArch64.Dp s₀ + BitVec.ofNat 64 (8 * k)) h.x1 h.x2
    (by rw [rdwr]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := VG.Proof.CmacTripleDes.AArch64.stR s₀) (by simp) (Region.contains_self _ _))
    (by rw [rdwr]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := VG.Proof.CmacTripleDes.AArch64.dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
  have v₁ : s₁.v = s.v := VG.AArch64.Tbl.runBlock_v VG.Proof.CmacTripleDes.AArch64.chainIn_v h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, h₁, ?_⟩)
  have x14₁ : s₁.gpr .x14 = VG.Proof.CmacTripleDes.AArch64.W s₀ := by rw [k₁ _ (by decide) (by decide), h.x14]
  have x15₁ : s₁.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.S s₀ := by rw [k₁ _ (by decide) (by decide), h.x15]
  have bp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₁ := UPre.block (hp := hp) x14₁ x15₁ (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr])
  have hS : VG.Proof.CmacTripleDes.AArch64.sch s₁ = Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.W s₀) := by
    rw [VG.Proof.CmacTripleDes.AArch64.sch, x14₁, m₁]; exact UPre.sched (hp := hp) h.frame
  have t₁ : VG.Proof.CmacTripleDes.AArch64.TInv s₁ s₁ := ⟨Same.refl _, rfl, rfl, h.consts.congr fun w _ _ _ _ => by rw [v₁],
    h.masks.congr fun p hp' => by
      obtain ⟨n5, -, -, -, -, n6, -⟩ := VG.Proof.CmacTripleDes.AArch64.maskRegs_ne p hp'
      exact k₁ _ n5 n6,
    fun i hi => by rw [x15₁, hS, m₁]; exact h.keys i hi⟩
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.enc_ok bp t₁) fun s₂ ⟨same₂, x14₂, ax₂, c₂, mk₂, ks₂⟩ => ?_)
  have f₂ : Frame [⟨VG.Proof.CmacTripleDes.AArch64.S s₀, 384⟩] s.mem s₂.mem := by rw [← m₁, ← x15₁]; exact same₂.frame
  have wr₂ : s₂.wr = [VG.Proof.CmacTripleDes.AArch64.stR s₀, VG.Proof.CmacTripleDes.AArch64.scrR s₀] := by rw [same₂.wr, wr₁, h.wr, hp.wr]
  have x1₂ : s₂.gpr .x1 = VG.Proof.CmacTripleDes.AArch64.St s₀ := by
    rw [same₂.keep .x1 (by simp [VG.Proof.CmacTripleDes.AArch64.outer]), k₁ _ (by decide) (by decide), h.x1]
  obtain ⟨s₃, h₃, x2₃, x3₃, k₃, m₃, sp₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.AArch64.chainOut_ok s₂ (P := VG.Proof.CmacTripleDes.AArch64.St s₀) x1₂
    (by rw [wr₂]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := VG.Proof.CmacTripleDes.AArch64.stR s₀) (by simp) (Region.contains_self _ _))
  have v₃ : s₃.v = s₂.v := VG.AArch64.Tbl.runBlock_v VG.Proof.CmacTripleDes.AArch64.chainOut_v h₃
  have hD := UPre.data (hp := hp) h.frame hk
  have fs : Frame [VG.Proof.CmacTripleDes.AArch64.stR s₀] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa using Region.contains_self (VG.Proof.CmacTripleDes.AArch64.St s₀) 8)
  have stD : ∀ {d n : Nat}, d + n ≤ 640 → ∀ r ∈ [VG.Proof.CmacTripleDes.AArch64.stR s₀],
      (⟨VG.Proof.CmacTripleDes.AArch64.S s₀ + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := fun hdn r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.st_scr.sub_right (UPre.scr_sub hdn)).symm
  refine WP.of_runBlock ⟨s₃, h₃, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_⟩⟩
  · rw [k₃ _ (by decide), x14₂, x14₁]
  · rw [k₃ _ (by decide), same₂.x15, x15₁]
  · rw [k₃ _ (by decide), x1₂]
  · rw [x2₃, same₂.keep .x2 (by simp [VG.Proof.CmacTripleDes.AArch64.outer]), k₁ _ (by decide) (by decide), h.x2, VG.Proof.CmacTripleDes.AArch64.x2_succ]
  · rw [x3₃, same₂.keep .x3 (by simp [VG.Proof.CmacTripleDes.AArch64.outer]), k₁ _ (by decide) (by decide), h.x3,
      show BitVec.ofNat 64 1 = 1 from rfl, VG.Proof.CmacTripleDes.AArch64.ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [sp₃, same₂.sp, sp₁, h.sp]
  · rw [rd₃, same₂.rd, rd₁, h.rd]
  · rw [wr₃, same₂.wr, wr₁, h.wr]
  · rw [m₃]
    exact (h.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨VG.Proof.CmacTripleDes.AArch64.S s₀, 456⟩, by simp [VG.Proof.CmacTripleDes.AArch64.chg], Region.sub_prefix (by decide : 384 ≤ 456)⟩)).writeW (r := VG.Proof.CmacTripleDes.AArch64.stR s₀) (by simp) _
      (by simpa using Region.contains_self (VG.Proof.CmacTripleDes.AArch64.St s₀) 8)
  · exact c₂.congr fun w _ _ _ _ => by rw [v₃]
  · exact mk₂.congr fun p hp' => k₃ _ (by
      obtain ⟨n5, -, -, -, -, -, -, -, -, -, n2, n3, -⟩ := VG.Proof.CmacTripleDes.AArch64.maskRegs_ne p hp'
      simp [n2, n3, n5])
  · rw [fs.readW (Region.contains_self _ _) (stD (by omega)) (by decide)]
    have := ks₂ i hi
    rw [x15₁, hS] at this
    exact this
  · have sv₂ : Spill.Saved (VG.Proof.CmacTripleDes.AArch64.S s₀) s₀.gpr VG.Proof.CmacTripleDes.AArch64.saveSlots s₂.mem :=
      h.slots.frame_in (lo := 384) (n := 72) saveSlots_facts.1 f₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by decide) (by decide)
    exact sv₂.frame fs fun q hq => stD (by have := saveSlots_facts.1 q hq; omega)
  · rw [m₃, ← le8_readW, Mem.readW_writeW_self64, ax₂, ax₁, ← tdesWith_le8, hS, le8_xor, le8_readW, le8_readW,
      h.state, hD, VG.Proof.CmacTripleDes.AArch64.take_succ_blks s₀ hk, chain_append, chain_single]

theorem loop_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.AArch64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.AArch64.N s₀) {s : State}
    (h : VG.Proof.CmacTripleDes.AArch64.LInv s₀ k s) : WP isa (.loop updBody (.nonzero .x .x3)) s (VG.Proof.CmacTripleDes.AArch64.LInv s₀ (VG.Proof.CmacTripleDes.AArch64.N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .nonzero .x .x3) (Q := VG.Proof.CmacTripleDes.AArch64.LInv s₀ (VG.Proof.CmacTripleDes.AArch64.N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = VG.Proof.CmacTripleDes.AArch64.N s₀ - j ∧ j < VG.Proof.CmacTripleDes.AArch64.N s₀ ∧ VG.Proof.CmacTripleDes.AArch64.LInv s₀ j t) ?_ (VG.Proof.CmacTripleDes.AArch64.N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.body_ok hp hk h) fun s' h' => ?_
  have hN : VG.Proof.CmacTripleDes.AArch64.N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have ev := VG.Proof.CmacTripleDes.AArch64.eval_nonzero (r := .x3) (x := VG.Proof.CmacTripleDes.AArch64.N s₀ - (k + 1)) (by omega) h'.x3
  by_cases hz : VG.Proof.CmacTripleDes.AArch64.N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show VG.Proof.CmacTripleDes.AArch64.N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], VG.Proof.CmacTripleDes.AArch64.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## The whole function -/

theorem x3_ofNat (s₀ : State) : s₀.gpr .x3 = BitVec.ofNat 64 (VG.Proof.CmacTripleDes.AArch64.N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [VG.Proof.CmacTripleDes.AArch64.N]

theorem update_wp {s₀ : State} (h0 : updateAArch64.pre s₀) :
    WP isa update s₀ fun s' =>
      updateAArch64.post s₀ s' ∧ ∀ i < 9, s'.gpr (savedReg i) = s₀.gpr (savedReg i) := by
  have hp := UPre.of h0
  have hN : VG.Proof.CmacTripleDes.AArch64.N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have sw := hp.scr_wrap
  let s₁ := (s₀.write .x .x14 (s₀.gpr .x0)).write .x .x15 ((s₀.write .x .x14 (s₀.gpr .x0)).gpr .x4)
  have g₁ : ∀ r, r ≠ .x14 → r ≠ .x15 → s₁.gpr r = s₀.gpr r := fun r h14 h15 => by
    simp only [s₁, gpr_write_of_ne _ _ _ h15, gpr_write_of_ne _ _ _ h14]
  have x14₁ : s₁.gpr .x14 = VG.Proof.CmacTripleDes.AArch64.W s₀ := by simp [s₁, gpr_write]
  have x15₁ : s₁.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.S s₀ := by simp [s₁, gpr_write]
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_nil], ?_⟩)
  have ev := VG.Proof.CmacTripleDes.AArch64.eval_zero (r := .x3) (x := VG.Proof.CmacTripleDes.AArch64.N s₀) hN (by rw [g₁ _ (by decide) (by decide), VG.Proof.CmacTripleDes.AArch64.x3_ofNat])
  have savedNe : ∀ i < 9, savedReg i ≠ .x14 ∧ savedReg i ≠ .x15 := by decide
  by_cases hn : VG.Proof.CmacTripleDes.AArch64.N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ⟨?_, fun i hi => ?_⟩)
      (fun h => by cases h)
    · show Spec.Aes.bytesAt s₁.mem (VG.Proof.CmacTripleDes.AArch64.St s₀) 8 = Spec.Cmac.chain (VG.Proof.CmacTripleDes.AArch64.ciph s₀) _ (VG.Proof.CmacTripleDes.AArch64.blks s₀)
      simp only [VG.Proof.CmacTripleDes.AArch64.blks, VG.Proof.CmacTripleDes.AArch64.N, hn, Spec.Cmac.blocksAt, List.range_zero, List.map_nil, Spec.Cmac.chain,
        List.foldl_nil]
      rfl
    · exact g₁ _ (savedNe i hi).1 (savedNe i hi).2
  refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
  have bp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₁ := UPre.block (hp := hp) x14₁ x15₁ rfl rfl
  apply WP.seq
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.prep_ok bp) fun s₂ h₂ => ?_
  have m₁ : s₁.mem = s₀.mem := rfl
  have inv₂ : VG.Proof.CmacTripleDes.AArch64.LInv s₀ 0 s₂ := by
    have hS : VG.Proof.CmacTripleDes.AArch64.sch s₁ = Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.W s₀) := by rw [VG.Proof.CmacTripleDes.AArch64.sch, x14₁]; rfl
    have outer₂ : ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.outer, s₂.gpr r = s₀.gpr r := fun r hr => by
      rw [h₂.same.keep r hr]
      simp only [VG.Proof.CmacTripleDes.AArch64.outer, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)
    have fr₂ : Frame (VG.Proof.CmacTripleDes.AArch64.chg s₀) s₀.mem s₂.mem := by
      rw [← m₁]
      exact h₂.same.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨VG.Proof.CmacTripleDes.AArch64.S s₀, 456⟩, by simp [VG.Proof.CmacTripleDes.AArch64.chg], by rw [x15₁]; exact fun _ h => h⟩
    refine ⟨by rw [h₂.x14, x14₁], by rw [h₂.same.x15, x15₁], outer₂ .x1 (by simp [VG.Proof.CmacTripleDes.AArch64.outer]),
      by rw [outer₂ .x2 (by simp [VG.Proof.CmacTripleDes.AArch64.outer])]; exact (BitVec.add_zero _).symm,
      by rw [outer₂ .x3 (by simp [VG.Proof.CmacTripleDes.AArch64.outer]), VG.Proof.CmacTripleDes.AArch64.x3_ofNat]; rfl, by rw [h₂.same.sp]; rfl,
      by rw [h₂.same.rd]; rfl, by rw [h₂.same.wr]; rfl, fr₂, h₂.consts, h₂.masks, fun i hi => ?_,
      fun p hp' => ?_, ?_⟩
    · have := h₂.keys i hi
      rw [x15₁, hS] at this
      exact this
    · rw [← x15₁, h₂.slots p hp']
      obtain ⟨j, hj, e⟩ := List.mem_map.mp hp'
      subst e
      exact g₁ _ (savedNe j (List.mem_range.mp hj)).1 (savedNe j (List.mem_range.mp hj)).2
    · show Spec.Aes.bytesAt s₂.mem (VG.Proof.CmacTripleDes.AArch64.St s₀) 8 = Spec.Cmac.chain (VG.Proof.CmacTripleDes.AArch64.ciph s₀) _ ((VG.Proof.CmacTripleDes.AArch64.blks s₀).take 0)
      rw [List.take_zero]
      simp only [Spec.Cmac.chain, List.foldl_nil]
      exact bytesAt_frame h₂.same.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [x15₁]; exact hp.st_scr.sub_right (Region.sub_prefix (by decide))) (by decide)
  apply WP.seq
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.loop_ok hp (by omega) inv₂) fun s₃ h₃ => ?_
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.restore_ok' bp (by rw [h₃.x15, x15₁]) (by rw [h₃.rd]; rfl) (by rw [h₃.wr]; rfl)
    (by rw [x15₁]; exact fun p hp' => by rw [h₃.slots p hp']; obtain ⟨j, hj, e⟩ := List.mem_map.mp hp'; subst e; exact (g₁ _ (savedNe j (List.mem_range.mp hj)).1 (savedNe j (List.mem_range.mp hj)).2).symm))
    fun s₄ h₄ => ⟨?_, fun i hi => ?_⟩
  · show Spec.Aes.bytesAt s₄.mem (VG.Proof.CmacTripleDes.AArch64.St s₀) 8 = Spec.Cmac.chain (VG.Proof.CmacTripleDes.AArch64.ciph s₀) _ (VG.Proof.CmacTripleDes.AArch64.blks s₀)
    rw [h₄.mem, h₃.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]
  · rw [h₄.gpr_of (.inl (List.mem_map.mpr ⟨_, VG.Proof.CmacTripleDes.AArch64.mem_saveSlots hi, rfl⟩))]
    exact g₁ _ (savedNe i hi).1 (savedNe i hi).2

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Finalize`. -/
section

/-!
# TDEA-CMAC on AArch64: `vg_cmac_triple_des_finalize`

The steps that form the last block `Mₙ` (§6.2 step 4) in `x5`, as a
little-endian word (`BPost`): `Mₙ* ⊕ K1` for a complete last block, else `Mₙ*`
copied a byte at a time onto the zeroed slot 6, `0x80` after it, XORed with
`K2`. The function then XORs in the chaining value `C`, encrypts it and stores
`CIPH_K(C ⊕ Mₙ)` as the state, the MAC (`macFull_split8`).
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes VG.Proof.Cmac

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them) and the scratch buffer `S`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L : Nat) : Prop where
  x0 : s₀.gpr .x0 = W
  x1 : s₀.gpr .x1 = St
  x2 : s₀.gpr .x2 = P
  x3 : (s₀.gpr .x3).toNat = L
  x4 : s₀.gpr .x4 = S
  rd : s₀.rd = [⟨W, 400⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 8⟩, ⟨S, 640⟩]
  key_st : (⟨W, 400⟩ : Region).Disjoint ⟨St, 8⟩
  key_scr : (⟨W, 400⟩ : Region).Disjoint ⟨S, 640⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 8⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 640⟩
  st_scr : (⟨St, 8⟩ : Region).Disjoint ⟨S, 640⟩
  key_wrap : W.toNat + 400 ≤ 2 ^ 64
  st_wrap : St.toNat + 8 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 640 ≤ 2 ^ 64
  len : L ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeAArch64.pre s₀) :
    VG.Proof.CmacTripleDes.AArch64.FPre s₀ (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x3).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- Slot 6, where a partial last block is formed. -/
abbrev slot6 (S : Addr) : Region := ⟨S + BitVec.ofNat 64 48, 8⟩

/-- What the branch on the length leaves: `Mₙ` in `x5`. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = W
  x15 : s.gpr .x15 = S
  x1 : s.gpr .x1 = St
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacTripleDes.AArch64.slot6 S] s₀.mem s.mem
  blk : le8 (s.gpr .x5) = VG.Proof.CmacTripleDes.AArch64.mn s₀.mem W P L

/-- What the first block leaves. -/
structure P1 (s₀ : State) (W St P S : Addr) (s : State) : Prop where
  x15 : s.gpr .x15 = S
  x14 : s.gpr .x14 = W
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = St
  x2 : s.gpr .x2 = P
  x3 : s.gpr .x3 = s₀.gpr .x3
  sp : s.sp = s₀.sp
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {s₀ : State} {W St P S : Addr} {L : Nat} (hp : VG.Proof.CmacTripleDes.AArch64.FPre s₀ W St P S L)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 640) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨S, 640⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 400) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨W, 400⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

end

theorem FPre.scrD {S : Addr} {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 640⟩ :=
  Offset.sub_base _ h

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem xor_comm (x y : List Byte) : Spec.Cmac.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## Copying the last bytes -/

/-- The copy loop's body. -/
abbrev copyBody : List Instr :=
  [.ldrb .x9 .x7 0, .strb .x9 .x6 0, .addImm .x .x7 .x7 1, .addImm .x .x6 .x6 1, .subImm .x .x8 .x8 1]

theorem byte_rt (b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [show 8 * 0 = 0 from rfl, BitVec.extractLsb'_eq_self, show BitVec.ofNat 64 0 = 0#64 from rfl,
    BitVec.add_zero] at this
  exact this

theorem copyStep_ok (s : State) {A B : Addr} (ha : s.gpr .x7 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x6 + BitVec.ofNat 64 0 = B)
    (r : InRegions (s.rd ++ s.wr) A 1) (w : InRegions s.wr B 1) :
    ∃ s', runBlock isa VG.Proof.CmacTripleDes.AArch64.copyBody s = some s' ∧ s'.mem = s.mem.writeW B (s.mem A) ∧
      s'.gpr .x7 = s.gpr .x7 + 1 ∧ s'.gpr .x6 = s.gpr .x6 + 1 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Proof.CmacTripleDes.AArch64.copyBody, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, r, w]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, VG.Proof.CmacTripleDes.AArch64.byte_rt, VG.Proof.CmacTripleDes.AArch64.read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

open VG.WriteBytes in
theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 8)
    (h7 : s.gpr .x7 = P) (h6 : s.gpr .x6 = C) (h8 : s.gpr .x8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P L) ∧
      s'.gpr .x6 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block VG.Proof.CmacTripleDes.AArch64.copyBody) (c := .nonzero .x .x8)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .x7 = P + BitVec.ofNat 64 i ∧
      t.gpr .x6 = C + BitVec.ofNat 64 i ∧ t.gpr .x8 = BitVec.ofNat 64 (L - i) ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h7]; simp, by rw [h6]; simp, by rw [h8, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x7, x6, x8, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x7', x6', x8', g', sp', rd', wr'⟩ := VG.Proof.CmacTripleDes.AArch64.copyStep_ok t
    (A := P + BitVec.ofNat 64 i) (B := C + BitVec.ofNat 64 i) (by rw [x7, BitVec.add_zero])
    (by rw [x6, BitVec.add_zero]) (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega),
      hlen]
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (i + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := VG.Proof.CmacTripleDes.AArch64.eval_nonzero (r := .x8) (x := L - (i + 1)) (by omega) x8''
  have gg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : i + 1 = L
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', x6, BitVec.add_assoc, VG.Proof.CmacTripleDes.AArch64.succ_ofNat, he], gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x7', x7, BitVec.add_assoc, VG.Proof.CmacTripleDes.AArch64.succ_ofNat], by rw [x6', x6, BitVec.add_assoc, VG.Proof.CmacTripleDes.AArch64.succ_ofNat], x8'', hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The straight-line pieces -/

theorem pre1_ok (s : State) {L : Nat} (hc : s.gpr .x3 = BitVec.ofNat 64 L) (hL : L ≤ 8) :
    ∃ s', runBlock isa [mov .x14 .x0, mov .x15 .x4, .subImm .x .x9 .x3 8] s = some s' ∧
      s'.gpr .x14 = s.gpr .x0 ∧ s'.gpr .x15 = s.gpr .x4 ∧
      (∀ r, r ∉ [Reg.x9, .x14, .x15] → s'.gpr r = s.gpr r) ∧
      isa.eval (.zero .x .x9) s' = some (decide (L = 8)) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], fun r hr => ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2]
  · show some (_ == 0) = _
    simp only [State.read, gpr_write_self, gpr_write_of_ne _ _ _ (show Reg.x3 ≠ .x15 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x3 ≠ .x14 by decide), BitVec.setWidth_eq, hc]
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]

/-- Two words XORed from `[pb + pd]` and `[qb + qd]` into `x5`. -/
theorem xor1_ok (s : State) (pb qb : Reg) (pd qd : Nat) {P Q : Addr}
    (hpd : pd % 8 = 0 ∧ pd < 32768) (hqd : qd % 8 = 0 ∧ qd < 32768)
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq' : qb ≠ .x5)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rq : InRegions (s.rd ++ s.wr) Q 8) :
    ∃ s', runBlock isa [.ldr .x .x5 pb pd, .ldr .x .x6 qb qd, .logic .eor .x .x5 .x5 .x6] s = some s' ∧
      s'.gpr .x5 = s.mem.readW P 64 ^^^ s.mem.readW Q 64 ∧ (∀ r, r ≠ .x5 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x5 (s.mem.readW (s.gpr pb + BitVec.ofNat 64 pd) 64)
  have rq' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr qb + BitVec.ofNat 64 qd) 8 := by
    rw [gpr_write_of_ne _ _ _ hq', hq]; exact rq
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x hpd (by rw [hp]; exact rp), runStep_some, runBlock_cons, exec_ldr_x hqd rq',
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [reduceCtorEq, ↓reduceIte, s₁, State.read, gpr_write, mem_write,
      BitVec.setWidth_eq, hp, hq', hq]
  · simp [s₁, gpr_write, h₁, h₂]

theorem zero_ok (s : State) {C : Addr} (hc : s.gpr .x15 + BitVec.ofNat 64 48 = C) (wc : InRegions s.wr C 8) :
    ∃ s', runBlock isa zero s = some s' ∧ s'.mem = s.mem.writeW C (0 : BitVec 64) ∧
      s'.gpr .x6 = C ∧ s'.gpr .x7 = s.gpr .x2 ∧ s'.gpr .x8 = s.gpr .x3 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, zero, mov, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, wr_write,
      Option.bind_some, BitVec.setWidth_eq, hc, wc]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write, ← hc], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, BitVec.setWidth_eq]
  rfl

theorem pad_ok (s : State) {B C K : Addr} (hb : s.gpr .x6 + BitVec.ofNat 64 0 = B)
    (hc : s.gpr .x15 + BitVec.ofNat 64 48 = C) (hk : s.gpr .x0 + BitVec.ofNat 64 392 = K)
    (w : InRegions s.wr B 1) (rc : InRegions (s.rd ++ s.wr) C 8) (rk : InRegions (s.rd ++ s.wr) K 8) :
    ∃ s', runBlock isa padK2 s = some s' ∧
      s'.mem = s.mem.writeW B (0x80 : Byte) ∧
      s'.gpr .x5 = (s.mem.writeW B (0x80 : Byte)).readW C 64 ^^^ (s.mem.writeW B (0x80 : Byte)).readW K 64 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, padK2, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.store, State.load, Size.bits, Size.bytes, State.read, gpr_write, mem_write, rd_write, wr_write,
      Option.bind_some, Option.map_some, BitVec.setWidth_eq, hb, hc, hk, w, rc, rk]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl, rfl⟩
  · simp only [mem_write, Mem.writeW, Nat.reduceDiv, Nat.reduceMul]
    rfl
  · simp only [gpr_write, ite_true, BitVec.setWidth_eq, Mem.writeW, Mem.readW, Nat.reduceDiv,
      Nat.reduceMul]
    rfl

/-! ## The last block -/

section
variable {s₀ : State} {W St P S : Addr} {L : Nat} (hp : VG.Proof.CmacTripleDes.AArch64.FPre s₀ W St P S L)
include hp

theorem FPre.keyD {d n : Nat} (h : d + n ≤ 400) {r : Region} (hr : Region.Sub r ⟨S, 640⟩) :
    (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right hr

theorem full_wp (hL : L = 8) {s : State} (h : VG.Proof.CmacTripleDes.AArch64.P1 s₀ W St P S s) :
    WP isa (.block full) s (VG.Proof.CmacTripleDes.AArch64.BPost s₀ W St P S L) := by
  subst hL
  have kw := hp.key_wrap
  obtain ⟨s', run, ax, g, sp, m, rd, wr⟩ := VG.Proof.CmacTripleDes.AArch64.xor1_ok s .x2 .x0 0 384 (P := P) (Q := W + BitVec.ofNat 64 384)
    (by decide) (by decide) (by rw [h.x2]; simp) (by rw [h.x0]) (by decide)
    (by rw [h.rd, h.wr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [h.rd, h.wr]; exact hp.inKey (d := 384) (n := 8) (by decide))
  refine WP.of_runBlock ⟨s', run, by rw [g _ (by decide) (by decide), h.x14],
    by rw [g _ (by decide) (by decide), h.x15], by rw [g _ (by decide) (by decide), h.x1], by rw [sp, h.sp],
    by rw [rd, h.rd], by rw [wr, h.wr], by rw [m, h.mem]; exact Frame.refl _ _, ?_⟩
  rw [ax, h.mem, le8_xor, le8_readW, le8_readW]
  simp only [VG.Proof.CmacTripleDes.AArch64.mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
  exact VG.Proof.CmacTripleDes.AArch64.xor_comm _ _

open VG.WriteBytes in
theorem partial_wp (hL : L < 8) {s : State} (h : VG.Proof.CmacTripleDes.AArch64.P1 s₀ W St P S s) :
    WP isa partialBlock s (VG.Proof.CmacTripleDes.AArch64.BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have hcx : s.gpr .x3 = BitVec.ofNat 64 L := by
    rw [h.x3, ← hp.x3]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 48 = C := ⟨_, rfl⟩
  have hc : s.gpr .x15 + BitVec.ofNat 64 48 = C := by rw [h.x15, hC]
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have sl : VG.Proof.CmacTripleDes.AArch64.slot6 S = ⟨C, 8⟩ := by rw [← hC]
  -- Zero the slot.
  obtain ⟨s₁, run₁, mem₁, x6₁, x7₁, x8₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.AArch64.zero_ok s hc
    (by rw [h.wr, ← hC]; exact hp.inScr (d := 48) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  let m₁ := s₀.mem.writeW C (0 : BitVec 64)
  have zf : s₁.mem = m₁ := by rw [mem₁, h.mem]
  have fz : Frame [⟨C, 8⟩] s₀.mem m₁ :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have lastZ : Spec.Aes.bytesAt m₁ P L = Spec.Aes.bytesAt s₀.mem P L :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.mem = writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L) ∧
      s₂.gpr .x6 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s₂.gpr r = s.gpr r) ∧
      s₂.sp = s₀.sp ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := VG.Proof.CmacTripleDes.AArch64.eval_zero (s := s₁) (r := .x3) (x := L) (by omega) (by rw [g₁ _ (by decide) (by decide)
                                     (by decide) (by decide), hcx])
    by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [x6₁]; simp,
        fun r h₁ h₂ h₃ h₄ _ => g₁ r h₁ h₂ h₃ h₄, by rw [sp₁, h.sp], by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (VG.Proof.CmacTripleDes.AArch64.copy_ok s₁ (by omega) hL (by rw [x7₁, h.x2]) x6₁ (by rw [x8₁, hcx])
        (fun i hi => by rw [rd₁, wr₁, h.rd, h.wr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, h.wr, ← hC, Offset.add_add]; exact hp.inScr (d := 48 + i) (n := 1) (by omega)) dPC) ?_
      rintro s₂ ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], x6₂, fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₂ r h₂ h₃ h₄ h₅, g₁ r h₁ h₂ h₃ h₄],
        by rw [sp₂, sp₁, h.sp], by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr]⟩
  · obtain ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩ := h₂
    have x15₂ : s₂.gpr .x15 = S := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x15]
    have x0₂ : s₂.gpr .x0 = W := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x0]
    obtain ⟨s₃, run₃, m₃, ax₃, g₃, sp₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.AArch64.pad_ok s₂ (B := C + BitVec.ofNat 64 L) (C := C)
      (K := W + BitVec.ofNat 64 392) (by rw [x6₂, BitVec.add_zero]) (by rw [x15₂, hC]) (by rw [x0₂])
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 48 + L) (n := 1) (by omega))
      (by rw [rd₂, wr₂, ← hC]; exact VG.Proof.CmacTripleDes.AArch64.wr_in (hp.inScr (d := 48) (n := 8) (by decide)))
      (by rw [rd₂, wr₂]; exact hp.inKey (d := 392) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .x5) (h₂ : r ≠ .x6) (h₃ : r ≠ .x7) (h₄ : r ≠ .x8) (h₅ : r ≠ .x9) :
        s₃.gpr r = s.gpr r := by rw [g₃ r h₁ h₂ h₅, g₂ r h₁ h₂ h₃ h₄ h₅]
    have hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have fB : Frame [⟨C, 8⟩] m₁ (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 8) (by omega) (by decide))
    have fW : Frame [⟨C, 8⟩] (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have f₃ : Frame [⟨C, 8⟩] s₀.mem s₃.mem := (fz.trans fB).trans fW
    have kD : (⟨W + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint ⟨C, 8⟩ := by
      rw [← hC]; exact hp.keyD (by decide) (FPre.scrD (by decide))
    have k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 392) 8 =
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 :=
      bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide)
    have pad : Spec.Aes.bytesAt s₃.mem C 8 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (8 - L - 1) := by
      have hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
        rw [← le8_readW, Mem.readW_writeW_self64]; decide
      have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem P L) (by rw [hlen]; exact hL) hz
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x14],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x15],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x1],
      by rw [sp₃, sp₂], by rw [rd₃, rd₂], by rw [wr₃, wr₂], by rw [sl]; exact f₃, ?_⟩
    rw [ax₃, ← m₃, le8_xor, le8_readW, le8_readW, pad, k2]
    simp only [VG.Proof.CmacTripleDes.AArch64.mn, Spec.Cmac.lastBlock, hlen, show L ≠ 8 by omega, ite_false]
    exact VG.Proof.CmacTripleDes.AArch64.xor_comm _ _

end

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L : Nat} (hp : VG.Proof.CmacTripleDes.AArch64.FPre s₀ W St P S L) :
    WP isa finPre s₀ (VG.Proof.CmacTripleDes.AArch64.BPost s₀ W St P S L) := by
  have hcx : s₀.gpr .x3 = BitVec.ofNat 64 L := by rw [← hp.x3]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, x14₁, x15₁, g₁, ev₁, sp₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.AArch64.pre1_ok s₀ hcx hp.len
  have h1 : VG.Proof.CmacTripleDes.AArch64.P1 s₀ W St P S s₁ := ⟨by rw [x15₁, hp.x4], by rw [x14₁, hp.x0],
    by rw [g₁ _ (by decide), hp.x0], by rw [g₁ _ (by decide), hp.x1], by rw [g₁ _ (by decide), hp.x2],
    g₁ _ (by decide), sp₁, m₁, rd₁, wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases hL : L = 8
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => VG.Proof.CmacTripleDes.AArch64.full_wp hp hL h1) (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => VG.Proof.CmacTripleDes.AArch64.partial_wp hp (by have := hp.len; omega) h1)

/-! ## The whole function -/

theorem xorSt_ok (s : State) {St : Addr} (hb : s.gpr .x1 = St) (r : InRegions (s.rd ++ s.wr) St 8) :
    ∃ s', runBlock isa [.ldr .x .x6 .x1 0, .logic .eor .x .x5 .x5 .x6, .rev .x5 .x5] s = some s' ∧
      s'.gpr .x5 = byteRev64 (s.gpr .x5 ^^^ s.mem.readW St 64) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x (by decide) (by rw [VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero, hb]; exact r), runStep_some,
      runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_rev, runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp (config := {decide := true}) only [State.read, gpr_write, ite_true, ite_false,
      BitVec.setWidth_eq, VG.Proof.CmacTripleDes.AArch64.rev64_eq, VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero, hb]
  · simp [gpr_write, h₁, h₂]

theorem storeSt_ok (s : State) {St : Addr} (hb : s.gpr .x1 = St) (w : InRegions s.wr St 8) :
    ∃ s', runBlock isa [.rev .x5 .x5, .str .x .x5 .x1 0] s = some s' ∧
      s'.mem = s.mem.writeW St (byteRev64 (s.gpr .x5)) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .x .x5 (rev64 (s.read .x .x5))
  have w' : InRegions s₁.wr (s₁.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    rw [VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero, gpr_write_of_ne _ _ _ (by decide), hb]; exact w
  refine ⟨_, by
    rw [runBlock_cons, exec_rev, runStep_some, runBlock_cons, exec_str_x (by decide) w', runStep_some,
      runBlock_nil], ?_⟩
  refine ⟨?_, rfl, rfl, rfl, fun r hr => gpr_write_of_ne _ _ _ hr⟩
  simp (config := {decide := true}) only [s₁, mem_write, State.read, gpr_write, ite_true, ite_false,
    BitVec.setWidth_eq, VG.Proof.CmacTripleDes.AArch64.rev64_eq, hb, VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero]

theorem finalize_wp {s₀ : State} (h0 : finalizeAArch64.pre s₀) :
    WP isa finalize s₀ fun s' =>
      finalizeAArch64.post s₀ s' ∧ ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs, s'.gpr r = s₀.gpr r := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .x0 = W at hp
  generalize hSt : s₀.gpr .x1 = St at hp
  generalize hP : s₀.gpr .x2 = P at hp
  generalize hS : s₀.gpr .x4 = S at hp
  generalize hL : (s₀.gpr .x3).toNat = L at hp
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have tw := hp.st_wrap
  refine WP.seq (WP.mono (WP.gprs (rs := VG.Proof.CmacTripleDes.AArch64.savedRegs) (VG.Proof.CmacTripleDes.AArch64.finPre_wp hp) (by lit_decide) (by lit_decide))
    fun s₁ ⟨h₁, sv₁⟩ => ?_)
  have rdwr₁ : s₁.rd ++ s₁.wr = [⟨W, 400⟩, ⟨P, L⟩, ⟨St, 8⟩, ⟨S, 640⟩] := by rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₂, run₂, ax₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := VG.Proof.CmacTripleDes.AArch64.xorSt_ok s₁ h₁.x1
    (by rw [rdwr₁]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have bp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₂ :=
    { sched := ⟨⟨W, 400⟩, by rw [rd₂, wr₂, h₁.rd, hp.rd]; simp, by rw [g₂ _ (by decide) (by decide), h₁.x14],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨S, 640⟩, by rw [wr₂, h₁.wr, hp.wr]; simp, by rw [g₂ _ (by decide) (by decide), h₁.x15],
        by show 456 ≤ 640; decide, by show 640 < 2 ^ 64; decide⟩
      disj := by
        rw [g₂ _ (by decide) (by decide), g₂ _ (by decide) (by decide), h₁.x14, h₁.x15]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right
          (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.block_ok bp) fun s₃ ⟨same₃, x14₃, ax₃, sv₃⟩ => ?_)
  have x1₃ : s₃.gpr .x1 = St := by rw [same₃.keep .x1 (by simp [VG.Proof.CmacTripleDes.AArch64.outer]), g₂ _ (by decide) (by decide), h₁.x1]
  obtain ⟨s₄, run₄, m₄, sp₄, rd₄, wr₄, g₄⟩ := VG.Proof.CmacTripleDes.AArch64.storeSt_ok s₃ x1₃
    (by rw [same₃.wr, wr₂, h₁.wr, hp.wr]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  refine WP.of_runBlock ⟨s₄, run₄, ⟨?_, fun r hr => ?_⟩⟩
  rotate_right
  · obtain ⟨i, hi, e⟩ := VG.Proof.CmacTripleDes.AArch64.mem_savedRegs hr
    subst e
    have : ∀ i < 9, savedReg i ≠ .x5 ∧ savedReg i ≠ .x6 := by decide
    rw [g₄ _ (this i hi).1, sv₃ i hi, g₂ _ (this i hi).1 (this i hi).2, sv₁ _ hr]
  intro hk msg hml hne hst
  rw [hW, hSt, hP, hL] at *
  have keyD (r : Region) (hr : Region.Sub r ⟨S, 640⟩) : (⟨W, 384⟩ : Region).Disjoint r :=
    (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right hr
  have hS' : VG.Proof.CmacTripleDes.AArch64.sch s₂ = Spec.TripleDes.scheduleAt s₀.mem W := by
    rw [VG.Proof.CmacTripleDes.AArch64.sch, g₂ _ (by decide) (by decide), h₁.x14, m₂]
    exact VG.Proof.CmacTripleDes.AArch64.scheduleAt_frame h₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact keyD _ (FPre.scrD (by decide))
  have hst₁ : le8 (s₁.mem.readW St 64) = Spec.Aes.bytesAt s₀.mem St 8 := by
    rw [le8_readW]
    exact bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (FPre.scrD (by decide))) (by decide)
  have hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem W)
  have hk' : Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 384) 8 ++
      Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 =
      (Spec.Cmac.subkeys (VG.Proof.CmacTripleDes.AArch64.ciphAt s₀.mem W) 8).1 ++ (Spec.Cmac.subkeys (VG.Proof.CmacTripleDes.AArch64.ciphAt s₀.mem W) 8).2 := by
    rw [show W + BitVec.ofNat 64 392 = W + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
      (Offset.add_add W 384 8).symm, ← bytesAt_split]; exact hk
  obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, VG.Proof.CmacTripleDes.AArch64.ciphAt, hks, length_le8])
  show Spec.Aes.bytesAt s₄.mem St 8 = _
  rw [m₄, ← le8_readW, Mem.readW_writeW_self64, ax₃, ax₂, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
    macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, VG.Proof.CmacTripleDes.AArch64.xor_comm]

/-- The stack pointer is unchanged. -/
theorem finalize_sp {s₀ s : State} {t : List Leak} (h : Exec isa finalize s₀ t s) : s.sp = s₀.sp := Exec.sp h

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Keys`. -/
section

/-!
# DES's key schedule on AArch64

`roundKeys` only moves bits of the key in `x5` to the round keys it
stores: the kernel checks it over the lane domain (`roundKeys_check`), and
`getLsbD_expandDesKey` says the bits are the specification's.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64
  VG.Proof.CmacTripleDes

/-- The round keys' slots, at `x2`. -/
def kCfg : Cfg := { base := .x2, slots := 16, ext := .x2, exts := 0 }

/-- Bit `q` of round key `j`: bit `rkSrc j q` of the key (input word 0). -/
def rkG (j q : Nat) : List Nat := if q < 48 then [rkSrc j q] else []

def kPost (e : Env (Nat × Nat)) : Bool := (List.range 16).all fun j => e.slot j == some (outWord (VG.Proof.CmacTripleDes.AArch64.rkG j))

theorem roundKeys_check : VG.AArch64.Straight.check (lanes 64 6) VG.Proof.CmacTripleDes.AArch64.kCfg (linExt 1) roundKeys (linEnv [(.x5, 0)]) VG.Proof.CmacTripleDes.AArch64.kPost = true := by
  rw [VG.Proof.CmacTripleDes.AArch64.roundKeys_eq]; lit_decide

theorem rkG_lt : ∀ j < 16, ∀ q < 64, ∀ a ∈ VG.Proof.CmacTripleDes.AArch64.rkG j q, a < 2 ^ 6 := by lit_decide

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by lit_decide

/-- The registers `roundKeys` writes. -/
def kWrites : List Reg := [.x6, .x7, .x11]

/-- Every register `roundKeys` writes is one of `kWrites`: checked once
for every instruction, rather than once for every other register. -/
theorem roundKeys_writes : roundKeys.all (fun i => (dstOf i).all kWrites.contains) = true := by
  rw [VG.Proof.CmacTripleDes.AArch64.roundKeys_eq]; lit_decide

theorem roundKeys_kept {r : Reg} (hr : r ∉ VG.Proof.CmacTripleDes.AArch64.kWrites) : roundKeys.all (fun i => dstOf i != some r) = true :=
  List.all_eq_true.mpr fun i hi => by
    have h := List.all_eq_true.mp VG.Proof.CmacTripleDes.AArch64.roundKeys_writes i hi
    cases hd : dstOf i with
    | none => rfl
    | some d =>
      rw [hd, Option.all_some] at h
      have hd' : d ∈ VG.Proof.CmacTripleDes.AArch64.kWrites := by simpa using h
      have hne : d ≠ r := fun e => hr (e ▸ hd')
      simpa using hne

/-- The round keys of the DES key in `x5`, in `[x2 + 8 j]`. -/
theorem roundKeys_ok {s : VG.AArch64.State} (hok : Ok VG.Proof.CmacTripleDes.AArch64.kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, s'.mem.readW (wordAddr (s.gpr .x2) j) 64 =
        ((Spec.TripleDes.expandDesKey (s.gpr .x5)).getD j 0).zeroExtend 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.CmacTripleDes.AArch64.kWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.AArch64.kCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.CmacTripleDes.AArch64.roundKeys_check
  let W : Nat → BitVec 64 := fun _ => s.gpr .x5
  have hrel : Rel (LaneRel 6 (assign W (2 ^ 6))) VG.Proof.CmacTripleDes.AArch64.kCfg (linExt 1) (linEnv [(.x5, 0)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun j a hj h => absurd hj (by simp [VG.Proof.CmacTripleDes.AArch64.kCfg])),
      fun _ _ h => by cases h⟩
    simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
    split at h
    · rename_i hr
      simp only [beq_iff_eq] at hr; subst hr
      simp only [Option.some.injEq, exists_eq_left'] at h; subst h
      exact inWord_rel W (i := 0) (by decide)
    · simp at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j hj => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at h
    have hw : ∀ q < 64, (s'.mem.readW (wordAddr (s.gpr .x2) j) 64).getLsbD q = xorBits W (VG.Proof.CmacTripleDes.AArch64.rkG j q) := by
      have := outWord_rel (VG.Proof.CmacTripleDes.AArch64.rkG_lt j hj) (p.rel.slot j _ (by simp only [VG.Proof.CmacTripleDes.AArch64.kCfg]; omega) h)
      rwa [p.base] at this
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [hw q hq, BitVec.getLsbD_setWidth, VG.Proof.CmacTripleDes.AArch64.rkG]
    by_cases h48 : q < 48
    · rw [ite_eq_left h48, getLsbD_expandDesKey _ hj h48]
      have := VG.Proof.CmacTripleDes.AArch64.rkSrc_lt j hj q h48
      simp [xorBits, bitOf, W, hq, Nat.mod_eq_of_lt this]
    · rw [ite_eq_right h48, BitVec.getLsbD_of_ge _ _ (by omega)]
      simp
  · have h := VG.Proof.CmacTripleDes.AArch64.roundKeys_kept hr
    simp [h]

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Init`. -/
section

/-!
# TDEA-CMAC on AArch64: `vg_cmac_triple_des_init`

`initPre` stores the three DES keys, as big-endian integers, in slots 6–8;
each iteration of the loop then writes one DES key's sixteen round keys
(`KInv`); the zero block is encrypted with them and doubled twice into the
subkeys.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Straight VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes
  VG.Proof.Cmac

section
variable (s₀ : State)

abbrev K : Addr := s₀.gpr .x0
abbrev Kl : Nat := (s₀.gpr .x1).toNat
abbrev O : Addr := s₀.gpr .x2
abbrev Sc : Addr := s₀.gpr .x3

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacTripleDes.AArch64.K s₀) (VG.Proof.CmacTripleDes.AArch64.Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 := byteRev64 (s₀.mem.readW (VG.Proof.CmacTripleDes.AArch64.K s₀ + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.AArch64.Kl s₀) j)) 64)

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨VG.Proof.CmacTripleDes.AArch64.K s₀, VG.Proof.CmacTripleDes.AArch64.Kl s₀⟩]
  wr : s₀.wr = [⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 400⟩, ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩]
  key_out : (⟨VG.Proof.CmacTripleDes.AArch64.K s₀, VG.Proof.CmacTripleDes.AArch64.Kl s₀⟩ : Region).Disjoint ⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 400⟩
  key_scr : (⟨VG.Proof.CmacTripleDes.AArch64.K s₀, VG.Proof.CmacTripleDes.AArch64.Kl s₀⟩ : Region).Disjoint ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩
  out_scr : (⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 400⟩ : Region).Disjoint ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩
  key_wrap : (VG.Proof.CmacTripleDes.AArch64.K s₀).toNat + VG.Proof.CmacTripleDes.AArch64.Kl s₀ ≤ 2 ^ 64
  out_wrap : (VG.Proof.CmacTripleDes.AArch64.O s₀).toNat + 400 ≤ 2 ^ 64
  scr_wrap : (VG.Proof.CmacTripleDes.AArch64.Sc s₀).toNat + 640 ≤ 2 ^ 64
  valid : VG.Proof.CmacTripleDes.AArch64.Kl s₀ = 16 ∨ VG.Proof.CmacTripleDes.AArch64.Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initAArch64.pre s₀) : VG.Proof.CmacTripleDes.AArch64.IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨a, b, c, d, e, f, g, h, i⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  x15 : s.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.Sc s₀
  x4 : s.gpr .x4 = VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 (48 + 8 * i)
  x2 : s.gpr .x2 = VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 (128 * i)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (3 - i)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW (VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 (48 + 8 * j)) 64 = VG.Proof.CmacTripleDes.AArch64.kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW (VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.AArch64.keyB s₀)).getD n 0
  frame : Frame [⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48, 24⟩, ⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 384⟩] s₀.mem s.mem

/-! ## The prologue -/

theorem keyOff_le {s₀ : State} (hp : VG.Proof.CmacTripleDes.AArch64.IPre s₀) {j : Nat} (hj : j < 3) : keyOff (VG.Proof.CmacTripleDes.AArch64.Kl s₀) j + 8 ≤ VG.Proof.CmacTripleDes.AArch64.Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega

section
variable {s₀ : State} (hp : VG.Proof.CmacTripleDes.AArch64.IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) : InRegions s₀.wr (VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) : InRegions s₀.wr (VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 400⟩) (by simp) (Offset.contains_base _ h (by have := hp.out_wrap; omega))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ VG.Proof.CmacTripleDes.AArch64.Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.CmacTripleDes.AArch64.K s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨VG.Proof.CmacTripleDes.AArch64.K s₀, VG.Proof.CmacTripleDes.AArch64.Kl s₀⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩] s₀.mem m) {d : Nat} (hd : d + 8 ≤ VG.Proof.CmacTripleDes.AArch64.Kl s₀) :
    m.readW (VG.Proof.CmacTripleDes.AArch64.K s₀ + BitVec.ofNat 64 d) 64 = s₀.mem.readW (VG.Proof.CmacTripleDes.AArch64.K s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨VG.Proof.CmacTripleDes.AArch64.K s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

end

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

theorem scrSub {S : Addr} {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 640⟩ :=
  Offset.sub_base _ h

/-- A DES key loaded, reversed and stored. -/
theorem keyWord_ok (s : State) (d o : Nat) (hd : d % 8 = 0 ∧ d < 32768) (ho : o % 8 = 0 ∧ o < 32768)
    (r : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8)
    (w : InRegions s.wr (s.gpr .x15 + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa (keyWord d o) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x15 + BitVec.ofNat 64 o)
        (byteRev64 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 d) 64)) ∧
      (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := (s.write .x .x5 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 d) 64))
  let s₂ := s₁.write .x .x5 (rev64 (s₁.read .x .x5))
  have w' : InRegions s₂.wr (s₂.gpr .x15 + BitVec.ofNat 64 o) 8 := by
    rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_of_ne _ _ _ (by decide)]; exact w
  refine ⟨_, by
    rw [keyWord, runBlock_cons, exec_ldr_x hd r, runStep_some, runBlock_cons, exec_rev, runStep_some,
      runBlock_cons, exec_str_x ho w', runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r hr => by simp [s₁, s₂, gpr_write, hr], rfl, rfl, rfl⟩
  simp only [reduceCtorEq, ↓reduceIte, s₁, s₂, mem_write, State.read, gpr_write,
    BitVec.setWidth_eq, VG.Proof.CmacTripleDes.AArch64.rev64_eq]

theorem initPre_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.AArch64.IPre s₀) : WP isa initPre s₀ (VG.Proof.CmacTripleDes.AArch64.KInv s₀ 0) := by
  have sw := hp.scr_wrap
  have kl : 16 ≤ VG.Proof.CmacTripleDes.AArch64.Kl s₀ := by rcases hp.valid with h | h <;> omega
  -- `mov x15, x3`.
  let s₁ := s₀.write .x .x15 (s₀.gpr .x3)
  have g₁ : ∀ r, r ≠ .x15 → s₁.gpr r = s₀.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  have x15₁ : s₁.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.Sc s₀ := by simp [s₁, gpr_write]
  obtain ⟨s₂, run₂, m₂, g₂, sp₂, rd₂, wr₂⟩ := VG.Proof.CmacTripleDes.AArch64.keyWord_ok s₁ 0 48 (by decide) (by decide)
    (by rw [g₁ _ (by decide)]; exact hp.inKey (d := 0) (n := 8) (by omega) (by decide))
    (by rw [x15₁]; exact hp.inScr (by decide))
  obtain ⟨s₃, run₃, m₃, g₃, sp₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.AArch64.keyWord_ok s₂ 8 56 (by decide) (by decide)
    (by rw [rd₂, wr₂, g₂ _ (by decide), g₁ _ (by decide)]; exact hp.inKey (d := 8) (n := 8) (by omega) (by decide))
    (by rw [wr₂, g₂ _ (by decide), x15₁]; exact hp.inScr (by decide))
  refine WP.seq (WP.of_runBlock ⟨_, by
    rw [VG.Proof.CmacTripleDes.AArch64.runBlock_append, VG.Proof.CmacTripleDes.AArch64.runBlock_append, VG.Proof.CmacTripleDes.AArch64.runBlock_append, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_mov, runStep_some, runBlock_nil,
      Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  let s₄ := s₃.write .x .x9 (s₃.read .x .x1 - BitVec.ofNat _ 16)
  have g₄ : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x15 → s₄.gpr r = s₀.gpr r := fun r h₁ h₂ h₃ => by
    rw [gpr_write_of_ne _ _ _ h₁, g₃ r h₂, g₂ r h₂, g₁ r h₃]
  have x15₄ : s₄.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.Sc s₀ := by rw [gpr_write_of_ne _ _ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), x15₁]
  -- The memory so far.
  have c48 : (⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48, 24⟩ : Region).Contains (VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48) (64 / 8) := by
    simpa using Offset.contains_base (VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48) (d := 0) (n := 8) (k := 24) (by decide) (by decide)
  have cAt (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 72) :
      (⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48, 24⟩ : Region).Contains (VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 d) (64 / 8) := by
    rw [show VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 d = VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 (d - 48) from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)
  have f₃ : Frame [⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48, 24⟩] s₀.mem s₃.mem := by
    rw [m₃, m₂, g₂ _ (by decide), x15₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c48).writeW (List.mem_singleton_self _) _
      (cAt 56 (by decide) (by decide))
  have fA : Frame [⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩] s₀.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, VG.Proof.CmacTripleDes.AArch64.scrSub (by decide)⟩
  have fA₂ : Frame [⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩] s₀.mem s₂.mem := by
    rw [m₂, x15₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have k0 : s₃.mem.readW (VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48) 64 = VG.Proof.CmacTripleDes.AArch64.kw s₀ 0 := by
    rw [m₃, g₂ _ (by decide), x15₁, VG.Proof.CmacTripleDes.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide), m₂, x15₁,
      Mem.readW_writeW_self64, g₁ _ (by decide)]
    simp [VG.Proof.CmacTripleDes.AArch64.kw, keyOff]
    rfl
  have k1 : s₃.mem.readW (VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 56) 64 = VG.Proof.CmacTripleDes.AArch64.kw s₀ 1 := by
    rw [m₃, g₂ _ (by decide), x15₁, Mem.readW_writeW_self64, g₂ _ (by decide), g₁ _ (by decide),
      hp.keyRead fA₂ (d := 8) (by omega)]
    simp [VG.Proof.CmacTripleDes.AArch64.kw, keyOff]
  -- The third DES key.
  have ev : isa.eval (.zero .x .x9) s₄ = some (decide (VG.Proof.CmacTripleDes.AArch64.Kl s₀ = 16)) := by
    show some (_ == 0) = _
    simp only [s₄, State.read, gpr_write_self, BitVec.setWidth_eq]
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide),
      show s₀.gpr .x1 = BitVec.ofNat 64 (VG.Proof.CmacTripleDes.AArch64.Kl s₀) by apply BitVec.eq_of_toNat_eq; simp,
      Offset.ofNat_sub_ofNat_beq (by have := (s₀.gpr .x1).isLt; omega) (by decide)]
  have third : ∀ d, d + 8 ≤ VG.Proof.CmacTripleDes.AArch64.Kl s₀ → d % 8 = 0 → d < 32768 →
      WP isa (.block [.ldr .x .x5 .x0 d]) s₄ fun s₅ =>
        s₅.gpr .x5 = s₀.mem.readW (VG.Proof.CmacTripleDes.AArch64.K s₀ + BitVec.ofNat 64 d) 64 ∧ (∀ r, r ≠ .x5 → s₅.gpr r = s₄.gpr r) ∧
        s₅.sp = s₀.sp ∧ s₅.mem = s₃.mem ∧ s₅.rd = s₀.rd ∧ s₅.wr = s₀.wr := by
    intro d hd h8 hl
    have r : InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x0 + BitVec.ofNat 64 d) 8 := by
      rw [g₄ _ (by decide) (by decide) (by decide)]
      show InRegions (s₃.rd ++ s₃.wr) _ 8
      rw [rd₃, wr₃, rd₂, wr₂]; exact hp.inKey (by omega) (by decide)
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ldr_x ⟨h8, hl⟩ r, runStep_some, runBlock_nil], ?_⟩
    refine ⟨?_, fun r hr => gpr_write_of_ne _ _ _ hr, by show s₃.sp = s₀.sp; rw [sp₃, sp₂]; rfl, rfl,
      by show s₃.rd = s₀.rd; rw [rd₃, rd₂]; rfl, by show s₃.wr = s₀.wr; rw [wr₃, wr₂]; rfl⟩
    rw [gpr_write_self, BitVec.setWidth_eq, g₄ _ (by decide) (by decide) (by decide)]
    exact hp.keyRead fA hd
  refine WP.seq (WP.mono (Q := fun (s₅ : State) =>
      s₅.gpr .x5 = s₀.mem.readW (VG.Proof.CmacTripleDes.AArch64.K s₀ + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.AArch64.Kl s₀) 2)) 64 ∧
        (∀ r, r ≠ .x5 → s₅.gpr r = s₄.gpr r) ∧ s₅.sp = s₀.sp ∧ s₅.mem = s₃.mem ∧ s₅.rd = s₀.rd ∧
        s₅.wr = s₀.wr) ?_ fun s₅ h₅ => ?_)
  · by_cases h16 : VG.Proof.CmacTripleDes.AArch64.Kl s₀ = 16
    · refine WP.ite true (by rw [ev]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega) (by decide) (by decide)
      rwa [show keyOff (VG.Proof.CmacTripleDes.AArch64.Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [ev]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      have h24 : VG.Proof.CmacTripleDes.AArch64.Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega
      have := third 16 (by omega) (by decide) (by decide)
      rwa [show keyOff (VG.Proof.CmacTripleDes.AArch64.Kl s₀) 2 = 16 by simp [keyOff, h24]]
  · obtain ⟨ax₅, g₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
    have x15₅ : s₅.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.Sc s₀ := by rw [g₅ _ (by decide), x15₄]
    let s₆ := s₅.write .x .x5 (rev64 (s₅.read .x .x5))
    have w : InRegions s₆.wr (s₆.gpr .x15 + BitVec.ofNat 64 64) 8 := by
      rw [gpr_write_of_ne _ _ _ (by decide), x15₅]; show InRegions s₅.wr _ 8
      rw [wr₅]; exact hp.inScr (by decide)
    refine WP.of_runBlock ⟨_, by
      rw [runBlock_cons, exec_rev, runStep_some, runBlock_cons, exec_str_x (by decide) w, runStep_some,
        runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_movz_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have mem₇ : s₅.mem.writeW (s₆.gpr .x15 + BitVec.ofNat 64 64) (s₆.gpr .x5) =
        s₃.mem.writeW (VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 64) (VG.Proof.CmacTripleDes.AArch64.kw s₀ 2) := by
      rw [gpr_write_of_ne _ _ _ (by decide), x15₅, m₅]
      simp only [s₆, gpr_write_self, State.read, BitVec.setWidth_eq, VG.Proof.CmacTripleDes.AArch64.rev64_eq, ax₅]
    have x15₆ : s₆.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.Sc s₀ := by rw [gpr_write_of_ne _ _ _ (by decide), x15₅]
    have g₆ : ∀ r, r ≠ .x5 → s₆.gpr r = s₅.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => absurd hn (by omega), ?_⟩
    · simp only [gpr_write, reduceCtorEq, ite_false]; exact x15₆
    · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq, State.read]
      rw [x15₆]
    · simp only [gpr_write, reduceCtorEq, ite_false]
      rw [g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide)]; simp
    · simp only [gpr_write, ite_true]; decide
    · exact sp₅
    · exact rd₅
    · exact wr₅
    · show (s₅.mem.writeW (s₆.gpr .x15 + BitVec.ofNat 64 64) (s₆.gpr .x5)).readW _ 64 = _
      rw [mem₇]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rw [VG.Proof.CmacTripleDes.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]; exact k0
      · rw [VG.Proof.CmacTripleDes.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]; exact k1
      · rw [Mem.readW_writeW_self64]
    · show Frame _ s₀.mem (s₅.mem.writeW (s₆.gpr .x15 + BitVec.ofNat 64 64) (s₆.gpr .x5))
      rw [mem₇]
      exact (f₃.mono fun r hr => by simp at hr; simp [hr]).writeW (r := ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 48, 24⟩)
        (by simp) _ (cAt 64 (by decide) (by decide))

/-! ## The round keys -/

theorem keysTail_ok (s : State) :
    ∃ s', runBlock isa [.addImm .x .x2 .x2 128, .addImm .x .x4 .x4 8, .subImm .x .x3 .x3 1] s = some s' ∧
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 128 ∧ s'.gpr .x4 = s.gpr .x4 + BitVec.ofNat 64 8 ∧
      s'.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ∉ [Reg.x2, .x3, .x4] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write, State.read], by simp [gpr_write, State.read], by simp [gpr_write, State.read],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [gpr_write, hr.1, hr.2.1, hr.2.2]

theorem keyStep_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.AArch64.IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : VG.Proof.CmacTripleDes.AArch64.KInv s₀ i s) :
    WP isa (.block keysBody) s (VG.Proof.CmacTripleDes.AArch64.KInv s₀ (i + 1)) := by
  have sw := hp.scr_wrap
  have ow := hp.out_wrap
  have rdwr : s.rd ++ s.wr = [⟨VG.Proof.CmacTripleDes.AArch64.K s₀, VG.Proof.CmacTripleDes.AArch64.Kl s₀⟩, ⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 400⟩, ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  rw [keysBody, List.append_assoc, WP.block_append_iff]
  have r4 : InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 0) 8 := by
    rw [rdwr, VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero, h.x4]
    exact VG.Proof.CmacTripleDes.AArch64.in_rw (r := ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ldr_x (by decide) r4, runStep_some, runBlock_nil], ?_⟩
  let s₁ := s.write .x .x5 (s.mem.readW (s.gpr .x4 + BitVec.ofNat 64 0) 64)
  have g₁ : ∀ r, r ≠ .x5 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  have ax₁ : s₁.gpr .x5 = s.mem.readW (s.gpr .x4) 64 := by
    simp only [s₁, gpr_write_self, BitVec.setWidth_eq, VG.Proof.CmacTripleDes.AArch64.add_ofNat_zero]
  rw [WP.block_append_iff]
  have x2₁ : s₁.gpr .x2 = VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 (128 * i) := by rw [g₁ _ (by decide), h.x2]
  have hok : Ok VG.Proof.CmacTripleDes.AArch64.kCfg s₁ := by
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.AArch64.kCfg]), by decide, fun k _ j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.AArch64.kCfg])⟩
    show InRegions s.wr _ 8
    rw [h.wr, hp.wr, show kCfg.base = .x2 from rfl, x2₁]
    exact ⟨⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 400⟩, by simp, contains_word (off := 128 * i) (n := 400) rfl
      (by simp only [VG.Proof.CmacTripleDes.AArch64.kCfg] at hk; omega) (by show 400 ≤ 400; decide) (by show 400 < 2 ^ 64; decide)⟩
  obtain ⟨s₂, run₂, rk₂, rd₂, wr₂, sp₂, g₂, f₂⟩ := VG.Proof.CmacTripleDes.AArch64.roundKeys_ok hok
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, x2₃, x4₃, x3₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.AArch64.keysTail_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have gk (r : Reg) (h₁ : r ∉ VG.Proof.CmacTripleDes.AArch64.kWrites) (h₂ : r ≠ .x5) : s₂.gpr r = s.gpr r := by rw [g₂ r h₁, g₁ r h₂]
  have slotR : slotRegion VG.Proof.CmacTripleDes.AArch64.kCfg s₁ = ⟨VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [slotRegion]; rw [show kCfg.base = .x2 from rfl, x2₁]; rfl
  rw [slotR] at f₂
  have dec : BitVec.ofNat 64 (3 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (3 - (i + 1)) :=
    VG.Proof.CmacTripleDes.AArch64.ofNat_sub_one (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩
  · rw [g₃ _ (by decide), gk _ (by decide) (by decide), h.x15]
  · rw [x4₃, gk _ (by decide) (by decide), h.x4, Offset.add_add, show 48 + 8 * i + 8 = 48 + 8 * (i + 1) by omega]
  · rw [x2₃, gk _ (by decide) (by decide), h.x2, Offset.add_add, show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [x3₃, gk _ (by decide) (by decide), h.x3, dec]
  · rw [sp₃, sp₂, ← h.sp]; rfl
  · rw [rd₃, rd₂, ← h.rd]; rfl
  · rw [wr₃, wr₂, ← h.wr]; rfl
  · rw [m₃, ← h.keys j hj]
    refine f₂.readW (r := ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀ + BitVec.ofNat 64 (48 + 8 * j), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (VG.Proof.CmacTripleDes.AArch64.scrSub (by omega))
  · rw [m₃]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn']
      refine f₂.readW (r := ⟨VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega⟩
      have hj : j < 16 := by omega
      have hk := VG.Proof.CmacTripleDes.AArch64.keyOff_le hp hi
      rw [show VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 (8 * (16 * i + j)) = wordAddr (s₁.gpr .x2) j by
          rw [x2₁, wordAddr, Offset.add_add, show 128 * i + 8 * j = 8 * (16 * i + j) by omega],
        rk₂ j hj, ax₁, h.x4, h.keys i hi, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₃]
    exact h.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 384⟩, by simp, Offset.sub_base _ (by omega)⟩)

theorem keys_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.AArch64.IPre s₀) {s : State} (h : VG.Proof.CmacTripleDes.AArch64.KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) (.nonzero .x .x3)) s (VG.Proof.CmacTripleDes.AArch64.KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .nonzero .x .x3) (Q := VG.Proof.CmacTripleDes.AArch64.KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ VG.Proof.CmacTripleDes.AArch64.KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.AArch64.keyStep_ok hp hi ht) fun t' h' => ?_
  have ev := VG.Proof.CmacTripleDes.AArch64.eval_nonzero (r := .x3) (x := 3 - (i + 1)) (by omega) h'.x3
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega, 3 - (i + 1), by omega, i + 1, rfl, by omega, h'⟩

/-! ## The subkeys -/

theorem dbl64_eq' (y : BitVec 64) :
    (y + y) ^^^ (((BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0)) - (y >>> 63)) &&&
      (BitVec.setWidth 64 (0x1b : BitVec 16) <<< (16 * 0))) = dbl64 y := by
  rw [← dbl64_eq]; rfl

theorem dbl_ok (s : State) (d : Nat) (hd : d % 8 = 0 ∧ d < 32768)
    (w : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (dbl d) s = some s' ∧
      s'.gpr .x5 = dbl64 (s.gpr .x5) ∧
      s'.mem = s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 d) (byteRev64 (dbl64 (s.gpr .x5))) ∧
      (∀ r, r ∉ [Reg.x5, .x6, .x7, .x11] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [dbl, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.store, Size.bits, Size.bytes, State.read, gpr_write, mem_write, wr_write, ite_true, ite_false,
      Option.bind_some, BitVec.setWidth_eq, hd, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    exact VG.Proof.CmacTripleDes.AArch64.dbl64_eq' _
  · simp only [BitVec.setWidth_eq, Mem.writeW, VG.Proof.CmacTripleDes.AArch64.rev64_eq, VG.Proof.CmacTripleDes.AArch64.dbl64_eq']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

theorem init_wp {s₀ : State} (h0 : initAArch64.pre s₀) :
    WP isa init s₀ fun s' => initAArch64.post s₀ s' ∧ ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs, s'.gpr r = s₀.gpr r := by
  have hp := IPre.of h0
  have sw := hp.scr_wrap
  have ow := hp.out_wrap
  refine WP.seq (WP.mono (WP.gprs (rs := VG.Proof.CmacTripleDes.AArch64.savedRegs) (VG.Proof.CmacTripleDes.AArch64.initPre_wp hp) (by lit_decide) (by lit_decide))
    fun s₁ ⟨h₁, sv₁⟩ => ?_)
  refine WP.seq (WP.mono (WP.gprs (rs := VG.Proof.CmacTripleDes.AArch64.savedRegs) (VG.Proof.CmacTripleDes.AArch64.keys_ok hp h₁) (by lit_decide) (by lit_decide))
    fun s₂ ⟨h₂, sv₂⟩ => ?_)
  refine WP.seq (WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons, VG.Proof.CmacTripleDes.AArch64.exec_movz_x (by decide),
      runStep_some, runBlock_nil], ?_⟩)
  let s₃ := (s₂.write .x .x14 (s₂.read .x .x2 - BitVec.ofNat _ 384)).write .x .x5
    ((0 : BitVec 16).setWidth 64 <<< (16 * 0))
  have g₃ : ∀ r, r ≠ .x5 → r ≠ .x14 → s₃.gpr r = s₂.gpr r := fun r h₁ h₂ => by
    simp only [s₃, gpr_write, h₁, h₂, ite_false]
  have x14₃ : s₃.gpr .x14 = VG.Proof.CmacTripleDes.AArch64.O s₀ := by
    simp only [s₃, gpr_write, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq]
    rw [h₂.x2, show 128 * 3 = 384 from rfl, BitVec.add_sub_cancel]
  have x15₃ : s₃.gpr .x15 = VG.Proof.CmacTripleDes.AArch64.Sc s₀ := by rw [g₃ _ (by decide) (by decide), h₂.x15]
  have ax₃ : s₃.gpr .x5 = 0 := by simp only [s₃, gpr_write_self]; decide
  have bp : VG.Proof.CmacTripleDes.AArch64.BlockPre s₃ :=
    { sched := ⟨⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 400⟩, by
          show _ ∈ s₂.rd ++ s₂.wr
          rw [h₂.rd, h₂.wr, hp.rd, hp.wr]; simp, by rw [x14₃],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩, by show _ ∈ s₂.wr; rw [h₂.wr, hp.wr]; simp, by rw [x15₃], by show 456 ≤ 640; decide,
        by show 640 < 2 ^ 64; decide⟩
      disj := by
        rw [x14₃, x15₃]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.block_ok bp) fun s₄ ⟨same₄, x14₄, ax₄, sv₄⟩ => ?_)
  -- The key schedule.
  have hsch₂ : Spec.TripleDes.scheduleAt s₂.mem (VG.Proof.CmacTripleDes.AArch64.O s₀) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.AArch64.keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega)]
  have f₄ : Frame [⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 456⟩] s₂.mem s₄.mem := by rw [← x15₃]; exact same₄.frame
  have outX : ∀ r ∈ [(⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 456⟩ : Region)], (⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.out_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  have hsch₄ : Spec.TripleDes.scheduleAt s₄.mem (VG.Proof.CmacTripleDes.AArch64.O s₀) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.AArch64.keyB s₀) := by
    rw [VG.Proof.CmacTripleDes.AArch64.scheduleAt_frame f₄ outX, hsch₂]
  rw [WP.block_append_iff]
  have x2₄ : s₄.gpr .x2 = VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384 := by
    rw [same₄.keep .x2 (by simp [VG.Proof.CmacTripleDes.AArch64.outer]), g₃ _ (by decide) (by decide), h₂.x2]
  have wr₄ : s₄.wr = [⟨VG.Proof.CmacTripleDes.AArch64.O s₀, 400⟩, ⟨VG.Proof.CmacTripleDes.AArch64.Sc s₀, 640⟩] := by rw [same₄.wr, ← hp.wr, ← h₂.wr]; rfl
  obtain ⟨s₅, run₅, ax₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := VG.Proof.CmacTripleDes.AArch64.dbl_ok s₄ 0 (by decide) (by
    rw [wr₄, x2₄, Offset.add_add]; rw [← hp.wr]; exact hp.inOut (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have x2₅ : s₅.gpr .x2 = VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384 := by rw [g₅ _ (by decide), x2₄]
  obtain ⟨s₆, run₆, ax₆, m₆, g₆, sp₆, rd₆, wr₆⟩ := VG.Proof.CmacTripleDes.AArch64.dbl_ok s₅ 8 (by decide) (by
    rw [wr₅, wr₄, x2₅, Offset.add_add]; rw [← hp.wr]; exact hp.inOut (by decide))
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  -- Memory.
  have c8 : (⟨VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 8)
      (64 / 8) := Offset.contains_base _ (by decide) (by decide)
  have c0 : (⟨VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 0)
      (64 / 8) := Offset.contains_base _ (by decide) (by decide)
  have f₆ : Frame [⟨VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384, 16⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅, x2₅, x2₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_⟩
  · show Spec.TripleDes.scheduleAt s₆.mem (VG.Proof.CmacTripleDes.AArch64.O s₀) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.AArch64.keyB s₀)
    rw [VG.Proof.CmacTripleDes.AArch64.scheduleAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by decide) (by omega)), hsch₄]
  · show Spec.Aes.bytesAt s₆.mem (VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.AArch64.keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.AArch64.keyB s₀))) 8).2
    have hk : VG.Proof.CmacTripleDes.AArch64.sch s₃ = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.AArch64.keyB s₀) := by rw [VG.Proof.CmacTripleDes.AArch64.sch, x14₃]; exact hsch₂
    rw [subkeys_tdes, m₆, x2₅, ax₅, m₅, x2₄, ax₄, ax₃, hk,
      show VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 0 = VG.Proof.CmacTripleDes.AArch64.O s₀ + BitVec.ofNat 64 384 from BitVec.add_zero _]
    exact bytesAt_store2 _ _ _ _
  · obtain ⟨i, hi, e⟩ := VG.Proof.CmacTripleDes.AArch64.mem_savedRegs hr
    subst e
    have : ∀ i < 9, savedReg i ∉ [Reg.x5, .x6, .x7, .x11] ∧ savedReg i ≠ .x5 ∧ savedReg i ≠ .x14 := by
      decide
    rw [g₆ _ (this i hi).1, g₅ _ (this i hi).1, sv₄ i hi, g₃ _ (this i hi).2.1 (this i hi).2.2,
      sv₂ _ hr, sv₁ _ hr]

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Implies`. -/
section

/-!
# TDEA-CMAC on AArch64: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initAArch64.Implies (initScratchContract AArch64.abi 0) := by
  sig_implies [initScratchContract, initScratchSig, Spec.Cmac.tdesInitPre, Spec.Cmac.tdesInitPost,
    VG.Proof.CmacTripleDes.AArch64.initAArch64, AArch64.abi,
    AArch64.argRegs] [initSat] using VG.Proof.CmacTripleDes.AArch64.initSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem update_implies : updateAArch64.Implies (updateScratchContract AArch64.abi 0) := by
  sig_implies [updateScratchContract, updateScratchSig, Spec.Cmac.tdesUpdatePost, VG.Proof.CmacTripleDes.AArch64.updateAArch64,
    AArch64.abi,
    AArch64.argRegs] [updSat] using VG.Proof.CmacTripleDes.AArch64.updSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finalize_implies : finalizeAArch64.Implies (finalizeScratchContract AArch64.abi 0) := by
  sig_implies [finalizeScratchContract, finalizeScratchSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, VG.Proof.CmacTripleDes.AArch64.finalizeAArch64, AArch64.abi,
    AArch64.argRegs] [finSat] using VG.Proof.CmacTripleDes.AArch64.finSat

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Verified`. -/
section

/-!
# TDEA-CMAC on AArch64: `Verified`

Correctness and constant time under this target's contracts (`Contract.lean`),
and the shared contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which imply them, with no stack: the
functions call nothing, and write only `x0`–`x17` and the callee-saved
registers the block saves and restores (`block_ok`).
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.AArch64

/-- The registers the ABI preserves that the code never writes. -/
def unsaved : List Reg := preserved.filter (· ∉ VG.Proof.CmacTripleDes.AArch64.savedRegs)

/-- The ABI's obligations, for code that keeps the registers of `savedRegs`,
writes none of the others it preserves and no vector register, and calls
nothing. -/
theorem abi_of {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => Q s' ∧ ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs, s'.gpr r = s.gpr r)
    (hc : c.allInstrs (fun i => unsaved.all fun r => dstOf i != some r) = true)
    (hn : c.noCalls = true) (hv : c.allInstrs keepsV = true) :
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Q s' := by
  obtain ⟨t, s', he, ⟨hq, hsv⟩, hg⟩ := WP.gprs h hc hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩, hq⟩
  by_cases hs : r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs
  · exact hsv r hs
  · exact hg r (List.mem_filter.mpr ⟨hr, by simpa using hs⟩)

theorem init_correct (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  VG.Proof.CmacTripleDes.AArch64.abi_of (VG.Proof.CmacTripleDes.AArch64.init_wp hs) (by lit_decide) (by lit_decide) (by lit_decide)

theorem update_correct (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' :=
  VG.Proof.CmacTripleDes.AArch64.abi_of (WP.mono (VG.Proof.CmacTripleDes.AArch64.update_wp hs) fun _ ⟨h, sv⟩ => ⟨h, fun r hr => by
    obtain ⟨i, hi, rfl⟩ := VG.Proof.CmacTripleDes.AArch64.mem_savedRegs hr; exact sv i hi⟩) (by lit_decide) (by lit_decide)
    (by lit_decide)

theorem finalize_correct (s : State) (hs : finalizeAArch64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeAArch64.post s s' :=
  VG.Proof.CmacTripleDes.AArch64.abi_of (VG.Proof.CmacTripleDes.AArch64.finalize_wp hs) (by lit_decide) (by lit_decide) (by lit_decide)

theorem init_verified : Verified AArch64.target init (initScratchContract AArch64.abi 0) :=
  Verified.of_correct VG.Proof.CmacTripleDes.AArch64.init_correct VG.Proof.CmacTripleDes.AArch64.init_ct VG.Proof.CmacTripleDes.AArch64.init_implies

theorem update_verified : Verified AArch64.target update (updateScratchContract AArch64.abi 0) :=
  Verified.of_correct VG.Proof.CmacTripleDes.AArch64.update_correct VG.Proof.CmacTripleDes.AArch64.update_ct VG.Proof.CmacTripleDes.AArch64.update_implies

theorem finalize_verified : Verified AArch64.target finalize (finalizeScratchContract AArch64.abi 0) :=
  Verified.of_correct VG.Proof.CmacTripleDes.AArch64.finalize_correct VG.Proof.CmacTripleDes.AArch64.finalize_ct VG.Proof.CmacTripleDes.AArch64.finalize_implies

end VG.Proof.CmacTripleDes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.AArch64.Frame`. -/
section

/-!
# TDEA-CMAC on AArch64, with its working space on the stack

The functions run their code, proved with the working space as an argument
(`Verified.lean`), in a frame of 640 bytes that allocates it
(`Verified.stackScratch`).
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.AArch64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition, without the
working space. -/
def initFrameSat : State := { VG.Proof.CmacTripleDes.AArch64.initSat with
                                           wr := [⟨0x2000, 400⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesInitContract AArch64.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, Spec.Cmac.tdesInitPre,
    Spec.Cmac.tdesInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using VG.Proof.CmacTripleDes.AArch64.initFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x3 init)
      (Spec.Cmac.tdesInitContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesInitPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.tdesInitPost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) VG.Proof.CmacTripleDes.AArch64.init_verified (by decide) (by decide) VG.Proof.CmacTripleDes.AArch64.initFrameSat_pre

theorem update_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x4 update)
      (Spec.Cmac.tdesUpdateContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesUpdateSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesUpdatePost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) VG.Proof.CmacTripleDes.AArch64.update_verified (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x4 finalize)
      (Spec.Cmac.tdesFinalizeContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesFinalizeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesFinalizePre AArch64.abi.ptrBits)
    (post := Spec.Cmac.tdesFinalizePost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) VG.Proof.CmacTripleDes.AArch64.finalize_verified (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))

end VG.Proof.CmacTripleDes.AArch64

end
