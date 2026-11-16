module

public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Layout
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Framework.AArch64.Linear
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `CmacTripleDes.AArch64.Spread`, which only this module used -/

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

@[expose] public section

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Bitslice
  VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64 VG.Impl.Tbl.AArch64 VG.Proof.CmacTripleDes

/-- Byte `e` of the gathering index: below 64, in the half of its key, at
the byte and the shift (`2 k`, in register `v k`) of its box's bits. -/
theorem gather_facts : ∀ e < 16,
    (gatherIndex e).toNat < 64 ∧ (gatherIndex e).toNat % 16 / 8 = e / 8 ∧
      8 * ((gatherIndex e).toNat % 8) + 2 * ((gatherIndex e).toNat / 16) =
        6 * (7 - boxOf (e % 8)) := by
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
  rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl
  · simp [hj]
  · simp [show ¬ 64 + j < 64 by omega_arith]

theorem getLsbD_vdword (x : BitVec 128) {h j : Nat} (hj : j < 64) :
    (vdword x h).getLsbD j = x.getLsbD (64 * h + j) := by
  simp [vdword, hj, Nat.add_comm]

theorem getLsbD_shr2 (x : BitVec 128) (k : Nat) {h j : Nat} (hh : h < 2) (hj : j < 64) :
    (shr2 x k).getLsbD (64 * h + j) = (decide (2 * k + j < 64) && x.getLsbD (64 * h + (2 * k + j))) := by
  rw [shr2, getLsbD_ofVDwords _ _ hh hj]
  rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;>
  · simp only [BitVec.getLsbD_ushiftRight, ite_true, ite_false, show (1 : Nat) ≠ 0 by decide]
    by_cases h' : 2 * k + j < 64
    · rw [getLsbD_vdword _ h', decide_eq_true h', Bool.true_and]
    · rw [decide_eq_false h', Bool.false_and, BitVec.getLsbD_of_ge _ _ (by omega_arith)]

theorem shr2_zero (x : BitVec 128) : shr2 x 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := getLsbD_shr2 x 0 (h := i / 64) (j := i % 64) (by omega_arith) (by omega_arith)
  rw [show 64 * (i / 64) + i % 64 = i by omega_arith, show 64 * (i / 64) + (2 * 0 + i % 64) = i by omega_arith,
    decide_eq_true (by omega_arith), Bool.true_and] at this
  exact this

/-- The table registers of the gathering `tbl`: `v0`–`v3`. -/
theorem repeat_v0 : ∀ k < 4, Nat.repeat VReg.succ k .v0 = [VReg.v0, .v1, .v2, .v3].getD k .v0 := by
  decide

theorem spreadV_ok (s : State) (hG : s.v .v5 = ofVBytes gatherIndex) (hM : s.v .v6 = bc 63)
    (hO : s.v .v7 = ofVDwords offsets offsets) :
    ∃ s', runBlock isa spreadV s = some s' ∧
      s'.v .v4 = ofVDwords (spread (vdword (s.v .v0) 0)) (spread (vdword (s.v .v0) 1)) ∧
      (∀ w, w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → s'.v w = s.v w) ∧
      s' = { s with v := s'.v } := by
  let x := s.v .v0
  let s₁ := s.setV .v1 (shr2 x 1)
  let s₂ := s₁.setV .v2 (shr2 x 2)
  let s₃ := s₂.setV .v3 (shr2 x 3)
  let T : BitVec 128 := ofVBytes fun i =>
    let idx := (vbyte (s₃.v .v5) i).toNat
    if idx < 16 * 4 then tableByte s₃.v .v0 idx else 0
  let s₄ := s₃.setV .v4 T
  let s₅ := s₄.setV .v4 (s₄.v .v4 &&& s₄.v .v6)
  let s₆ := s₅.setV .v4 (s₅.v .v4 ^^^ s₅.v .v7)
  have r₃ : ∀ k < 4, s₃.v ([VReg.v0, .v1, .v2, .v3].getD k .v0) = shr2 x k := by
    intro k hk
    rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · simp only [List.getD_cons_zero, s₃, s₂, s₁, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1),
        shr2_zero]
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
  have hv : ∀ (t : State) (r : VReg) (y : BitVec 128), t = { s with v := t.v } →
      t.setV r y = { s with v := (t.setV r y).v } := by
    intro t r y h; rw [h]; rfl
  refine ⟨s₆, ?_, ?_, fun w h1 h2 h3 h4 => ?_,
    hv _ _ _ (hv _ _ _ (hv _ _ _ (hv _ _ _ (hv _ _ _ (hv _ _ _ rfl)))))⟩
  · rw [spreadV]
    rfl
  · have a₆ : s₆.v .v4 = s₅.v .v4 ^^^ s₅.v .v7 := v_setV_self _ _ _
    have a₅ : s₅.v .v4 = s₄.v .v4 &&& s₄.v .v6 := v_setV_self _ _ _
    have a₄ : s₄.v .v4 = T := v_setV_self _ _ _
    rw [a₆, v7₅, a₅, v6₄, a₄]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    -- In the half `h` of the key, position `j`, byte `e`, bit `t`.
    obtain ⟨h, j, hh, hj, rfl⟩ : ∃ h j, h < 2 ∧ j < 64 ∧ i = 64 * h + j :=
      ⟨i / 64, i % 64, by omega_arith, by omega_arith, by omega_arith⟩
    have he : 8 * h + j / 8 < 16 := by omega_arith
    obtain ⟨g64, ghalf, gpos⟩ := gather_facts (8 * h + j / 8) he
    have hT : T.getLsbD (64 * h + j) = (vbyte (shr2 x ((gatherIndex (8 * h + j / 8)).toNat / 16))
        ((gatherIndex (8 * h + j / 8)).toNat % 16)).getLsbD (j % 8) := by
      have := getLsbD_ofVBytes (fun i =>
        let idx := (vbyte (s₃.v .v5) i).toNat
        if idx < 16 * 4 then tableByte s₃.v .v0 idx else 0) he (show j % 8 < 8 by omega_arith)
      rw [show 8 * (8 * h + j / 8) + j % 8 = 64 * h + j by omega_arith] at this
      rw [show T = _ from rfl, this]
      simp only
      rw [v5₃, vbyte_ofVBytes _ he, ite_eq_left (by omega_arith), tableByte,
        repeat_v0 _ (by omega_arith), r₃ _ (by omega_arith)]
    have hbc : (bc 63).getLsbD (64 * h + j) = decide (j % 8 < 6) := by
      have := getLsbD_ofVBytes (fun _ => (63 : BitVec 8)) he (show j % 8 < 8 by omega_arith)
      rw [show 8 * (8 * h + j / 8) + j % 8 = 64 * h + j by omega_arith] at this
      rw [bc, this]
      have : ∀ t < 8, (63 : BitVec 8).getLsbD t = decide (t < 6) := by decide
      exact this _ (by omega_arith)
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, hT, hbc, getLsbD_ofVDwords _ _ hh hj,
      getLsbD_ofVDwords _ _ hh hj]
    have hj8 : j = 8 * (j / 8) + j % 8 := by omega_arith
    have hsp : ∀ (K : BitVec 64), (spread K).getLsbD j =
        if j % 8 < 6 then K.getLsbD (6 * (7 - boxOf (j / 8)) + j % 8) else offsets.getLsbD j := by
      intro K
      rw [hj8, getLsbD_spread K (by omega_arith) (by omega_arith), offsets_bits _ (by omega_arith) _ (by omega_arith)]
      simp only [show (8 * (j / 8) + j % 8) % 8 = j % 8 by omega_arith,
        show (8 * (j / 8) + j % 8) / 8 = j / 8 by omega_arith]
      by_cases h6 : j % 8 < 6
      · simp [h6]
      · simp [h6, show 6 ≤ j % 8 by omega_arith]
    have hoff : j % 8 < 6 → offsets.getLsbD j = false := by
      intro h6
      rw [hj8, offsets_bits _ (by omega_arith) _ (by omega_arith), decide_eq_false (by omega_arith), Bool.false_and]
    have hbox : (8 * h + j / 8) % 8 = j / 8 := by omega_arith
    rw [hbox] at gpos
    -- The gathered bit.
    have hg : j % 8 < 6 → (vbyte (shr2 x ((gatherIndex (8 * h + j / 8)).toNat / 16))
        ((gatherIndex (8 * h + j / 8)).toNat % 16)).getLsbD (j % 8) =
        (vdword x h).getLsbD (6 * (7 - boxOf (j / 8)) + j % 8) := by
      intro h6
      rw [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true (by omega_arith), Bool.true_and,
        show 8 * ((gatherIndex (8 * h + j / 8)).toNat % 16) + j % 8 =
          64 * h + (8 * ((gatherIndex (8 * h + j / 8)).toNat % 8) + j % 8) by omega_arith,
        getLsbD_shr2 _ _ hh (by omega_arith), decide_eq_true (by omega_arith), Bool.true_and,
        getLsbD_vdword _ (by omega_arith)]
      congr 1
      omega_arith
    have hite : ∀ (a b : BitVec 64), (if h = 0 then a.getLsbD j else b.getLsbD j) =
        ([a, b].getD h 0).getLsbD j := by
      intro a b; rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;> rfl
    have hvd : ∀ h' < 2, vdword x h' = [vdword x 0, vdword x 1].getD h' 0 := by
      intro h' hh'; rcases (by omega_arith : h' = 0 ∨ h' = 1) with rfl | rfl <;> rfl
    have hsp' : ([spread (vdword x 0), spread (vdword x 1)].getD h 0) = spread (vdword x h) := by
      rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;> rfl
    rw [hite, hite, hsp', show ([offsets, offsets].getD h 0) = offsets by
      rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;> rfl, hsp]
    by_cases h6 : j % 8 < 6
    · rw [decide_eq_true h6, Bool.and_true, hg h6, hoff h6, Bool.xor_false, ite_eq_left h6]
    · rw [decide_eq_false h6, Bool.and_false, Bool.false_xor, ite_eq_right h6]
  · simp only [s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h4, v_setV_of_ne _ _ h3,
      v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h1]

end VG.Proof.CmacTripleDes.AArch64

end

end

/-! ### `CmacTripleDes.AArch64.Round`, which only this module used -/

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

@[expose] public section

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Straight VG.AArch64.Tbl VG.Bitslice
  VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64 VG.Impl.Tbl.AArch64 VG.Proof.CmacTripleDes

/-- What the rounds keep in the vector registers: the tables, and 64, 128
and 192 in every byte of `v4`, `v5` and `v6`. -/
structure Consts (s : State) : Prop where
  tab : ∀ k < 256, tbyte s.v k = sTable k
  c64 : s.v .v4 = bc 64
  c128 : s.v .v5 = bc 128
  c192 : s.v .v6 = bc 192

theorem Consts.congr {s s' : State} (h : Consts s)
    (hv : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s'.v w = s.v w) : Consts s' where
  tab k hk := by rw [tbyte_congr (fun r a b c d _ _ => hv r a b c d) k hk]; exact h.tab k hk
  c64 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c64
  c128 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c128
  c192 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c192

/-! ## The index -/

/-- The step of the key pointer. -/
def kstep (down : Bool) : Instr := if down then .subImm .x .x10 .x10 8 else .addImm .x .x10 .x10 8

theorem exec_kstep (s : State) (down : Bool) :
    exec (kstep down) s =
      some (s.write .x .x10 (if down then s.gpr .x10 - 8 else s.gpr .x10 + 8)) := by
  cases down
  · simp only [kstep, Bool.false_eq_true, ite_false, exec_addImm_x (by decide : 8 < 4096),
      State.read, BitVec.setWidth_eq]; rfl
  · simp only [kstep, ite_true, exec_subImm_x (by decide : 8 < 4096), State.read,
      BitVec.setWidth_eq]; rfl

theorem sIn_eq (b : Reg) (down : Bool) : sIn b down =
    [.ldr .x .x5 .x10 0, kstep down, .logic .eor .x .x5 .x5 b, .vop (.ins .d2 .v0 0 .x5),
     .vop (.logic .eor .v1 .v0 .v4), .vop (.logic .eor .v2 .v0 .v5),
     .vop (.logic .eor .v3 .v0 .v6)] := rfl

theorem vbyte_setLane0 (x : BitVec 128) (y : BitVec 64) {e : Nat} (he : e < 8) :
    vbyte (setLane x 64 0 y) e = y.extractLsb' (8 * e) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, setLane, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, Nat.mul_zero, Nat.sub_zero,
    show 8 * e + i < 128 by omega_arith, show 8 * e + i < 64 by omega_arith, show ¬ 8 * e + i < 0 by omega_arith]
  simp

theorem sIn_ok (s : State) {b : Reg} (hb5 : b ≠ .x5) (hb10 : b ≠ .x10) (down : Bool)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x10) 8) (hc : Consts s) :
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
  · rw [sIn_eq, runBlock_cons, exec_ldr_x (by decide) hk', runStep_some, runBlock_cons,
      exec_kstep, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons,
      exec_insd _ _ _ (by decide), runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, exec_eorv, runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_nil]
  · rw [v0₇, vbyte_setLane0 _ _ he]
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

theorem exec_umovx0 (s : State) (d : Reg) (n : VReg) :
    exec (.umov .x d n 0) s = some (s.write .x d ((s.v n).extractLsb' 0 64)) := by
  simp [exec, Size.bits]

theorem extract_vbyte (v : BitVec 128) {l : Nat} (hl : l < 8) :
    ((v.extractLsb' 0 64).extractLsb' (8 * l) 8) = vbyte v l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [vbyte, hi, show 8 * l + i < 64 by omega_arith]

/-- The S-boxes' outputs `y`, in `x5`: byte `l` is the table's byte at the
index's byte `l`. -/
theorem sOut_ok {s : State} (I : Nat → BitVec 8)
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
  · rw [sOut, runBlock_cat_some rund (by rw [runBlock_cons, exec_umovx0, runStep_some, runBlock_nil])]
  · simp only [t, gpr_write_self, BitVec.setWidth_eq]
    rw [extract_vbyte _ hl, d0 l (by omega_arith)]
  · simp only [t, gpr_write_of_ne _ _ _ hr, dv.gpr]
  · simp only [t, v_write]; exact dv.2 w (by simp [a, b, c, e])
  · simp only [t, mem_write, dv.mem]
  · simp only [t, rd_write, dv.rd]
  · simp only [t, wr_write, dv.wr]
  · simp only [t, sp_write]; rw [dv.1]

/-! ## `P` -/

/-- No memory. -/
def oCfg : Cfg := { base := .x15, slots := 0, ext := .x14, exts := 0 }

theorem oCfg_ok (s : State) : Ok oCfg s :=
  ⟨fun k hk => absurd hk (by simp [oCfg]), fun k hk => absurd hk (by simp [oCfg]), by decide,
    fun k hk => absurd hk (by simp [oCfg])⟩

theorem frame_oCfg {s : State} {m m' : Mem} (h : Frame [slotRegion oCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, oCfg, Region.Contains]

/-- The masks and their registers. -/
def maskConsts : List (Reg × BitVec 64) :=
  pGroups.zipIdx.map fun (g, k) => (maskReg k, BitVec.ofNat 64 g.2)

/-- The mask registers hold the masks. -/
def Masks (s : State) : Prop := ∀ r v, (r, v) ∈ maskConsts → s.gpr r = v

/-- The mask registers are none of the round's others. -/
theorem maskRegs_ne : ∀ p ∈ maskConsts, p.1 ≠ .x5 ∧ p.1 ≠ .x10 ∧ p.1 ≠ .x11 ∧ p.1 ≠ .x12 ∧
    p.1 ≠ .x16 ∧ p.1 ≠ .x6 ∧ p.1 ≠ .x7 ∧ p.1 ≠ .x14 ∧ p.1 ≠ .x15 ∧ p.1 ≠ .x1 ∧ p.1 ≠ .x2 ∧
    p.1 ≠ .x3 ∧ p.1 ≠ .x4 := by
  lit_decide

theorem Masks.congr {s s' : State} (h : Masks s) (hg : ∀ p ∈ maskConsts, s'.gpr p.1 = s.gpr p.1) :
    Masks s' := fun r v hp => by rw [hg (r, v) hp]; exact h r v hp

theorem ySrc_bound : ∀ p < 64, (ySrc p).all (· < 64) = true := by lit_decide

theorem ySrc_lt {p q : Nat} (hp : p < 64) (h : ySrc p = some q) : q < 64 := by
  have := ySrc_bound p hp
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
    check (lanes 64 7) oCfg (linExt 2) (pOut .x11) (linEnvC (pIns .x11) maskConsts)
      (linPost 7 [(.x11, pG)]) = true := by
  lit_decide

theorem pOut12_check :
    check (lanes 64 7) oCfg (linExt 2) (pOut .x12) (linEnvC (pIns .x12) maskConsts)
      (linPost 7 [(.x12, pG)]) = true := by
  lit_decide

theorem pOut11_masks :
    maskConsts.all (fun p => (pOut .x11).all fun i => !clobbers i p.1) = true := by
  lit_decide

theorem pOut12_masks :
    maskConsts.all (fun p => (pOut .x12).all fun i => !clobbers i p.1) = true := by
  lit_decide

/-- The registers `pOut` keeps. -/
def pKept : List Reg := [.x1, .x2, .x3, .x4, .x5, .x10, .x14, .x15, .x16]

theorem pOut11_kept : (.x12 :: pKept).all (fun r => (pOut .x11).all fun i => !clobbers i r) = true := by
  lit_decide

theorem pOut12_kept : (.x11 :: pKept).all (fun r => (pOut .x12).all fun i => !clobbers i r) = true := by
  lit_decide

theorem pOut11_v : (pOut .x11).all (fun i => vdstOf i == none) = true := by lit_decide
theorem pOut12_v : (pOut .x12).all (fun i => vdstOf i == none) = true := by lit_decide

theorem pOut_ok (s : State) {a b : Reg} (hab : (a = .x11 ∧ b = .x12) ∨ (a = .x12 ∧ b = .x11))
    (hm : Masks s) :
    ∃ s', runBlock isa (pOut a) s = some s' ∧
      (∀ p < 64, (s'.gpr a).getLsbD p =
        ((match ySrc p with | some q => (s.gpr .x5).getLsbD q | none => false) ^^ (s.gpr a).getLsbD p)) ∧
      (∀ r ∈ b :: pKept, s'.gpr r = s.gpr r) ∧ Masks s' ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let W (i : Nat) : BitVec 64 := if i = 0 then s.gpr .x5 else s.gpr a
  have go : ∀ (hchk : check (lanes 64 7) oCfg (linExt 2) (pOut a) (linEnvC (pIns a) maskConsts)
        (linPost 7 [(a, pG)]) = true)
      (hkept : (b :: pKept).all (fun r => (pOut a).all fun i => !clobbers i r) = true)
      (hmk : maskConsts.all (fun p => (pOut a).all fun i => !clobbers i p.1) = true)
      (hv : (pOut a).all (fun i => vdstOf i == none) = true),
      ∃ s', runBlock isa (pOut a) s = some s' ∧
      (∀ p < 64, (s'.gpr a).getLsbD p =
        ((match ySrc p with | some q => (s.gpr .x5).getLsbD q | none => false) ^^ (s.gpr a).getLsbD p)) ∧
      (∀ r ∈ b :: pKept, s'.gpr r = s.gpr r) ∧ Masks s' ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    intro hchk hkept hmk hv
    obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_okC hchk (oCfg_ok s) W
      (fun r i hri => by
        simp only [pIns, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
        rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
      hm (fun j hj => absurd hj (by simp [oCfg]))
    refine ⟨s', hs', fun p hp => ?_, fun r hr => hoth r (List.all_eq_true.mp hkept r hr),
      hm.congr fun p hp => hoth p.1 (List.all_eq_true.mp hmk p hp), ?_, ?_, hrd, hwr, hsp⟩
    · rw [hout a pG (by simp) p hp, pG]
      split
      · rename_i q hq
        have hq64 : q < 64 := ySrc_lt hp hq
        simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, W,
          Nat.div_eq_of_lt hq64, Nat.mod_eq_of_lt hq64, show (64 + p) / 64 = 1 by omega_arith,
          show (64 + p) % 64 = p by omega_arith, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]
      · simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, W, Bool.false_xor,
          show (64 + p) / 64 = 1 by omega_arith, show (64 + p) % 64 = p by omega_arith,
          show (1 : Nat) ≠ 0 by decide, ite_false]
    · exact runBlock_v hv hs'
    · exact frame_oCfg hfr
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact go pOut11_check pOut11_kept pOut11_masks pOut11_v
  · exact go pOut12_check pOut12_kept pOut12_masks pOut12_v

/-! ## The round -/

theorem runBlock_append (a b : List Instr) (s : State) :
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
  rw [← hy _ (laneOf_lt i hi), BitVec.getLsbD_extractLsb', decide_eq_true hpos, Bool.true_and]

theorem posOf_lt : ∀ i < 8, ∀ q < 4, posOf i q < 8 := by decide

/-- One round: `a := a ⊕ f(b, K)`, spread, with the spread round key at
`x10`, moving it to the next. -/
theorem round_ok {s : State} {a b : Reg} (hab : (a = .x11 ∧ b = .x12) ∨ (a = .x12 ∧ b = .x11))
    (down : Bool) (hc : Consts s) (hm : Masks s) (hk : InRegions (s.rd ++ s.wr) (s.gpr .x10) 8)
    {l r : BitVec 32} {K : BitVec 64} (hl : s.gpr a = spreadW l) (hr : s.gpr b = spreadW r)
    (hK : s.mem.readW (s.gpr .x10) 64 = spread K) :
    ∃ s', runBlock isa (round a b down) s = some s' ∧
      s'.gpr a = spreadW (l ^^^ Spec.TripleDes.roundFunction r (K.setWidth 48)) ∧
      s'.gpr .x10 = (if down then s.gpr .x10 - 8 else s.gpr .x10 + 8) ∧
      (∀ g ∈ b :: [.x1, .x2, .x3, .x4, .x14, .x15, .x16], s'.gpr g = s.gpr g) ∧
      Consts s' ∧ Masks s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hb5 : b ≠ .x5 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hb10 : b ≠ .x10 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have ha5 : a ≠ .x5 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have ha10 : a ≠ .x10 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  obtain ⟨s₁, h₁, i₀, i₁, i₂, i₃, x10₁, g₁, v₁, m₁, rd₁, wr₁, sp₁⟩ := sIn_ok s hb5 hb10 down hk hc
  have hc₁ : Consts s₁ := hc.congr v₁
  let I : Nat → BitVec 8 := fun e => vbyte (s₁.v .v0) e
  obtain ⟨s₂, h₂, y₂, g₂, v₂, m₂, rd₂, wr₂, sp₂⟩ := sOut_ok (s := s₁) I (fun _ _ => rfl)
    (fun e he => i₁ e he) (fun e he => i₂ e he) (fun e he => i₃ e he)
  have hc₂ : Consts s₂ := hc₁.congr v₂
  have hm₂ : Masks s₂ := hm.congr fun p hp => by
    obtain ⟨n5, n10, -⟩ := maskRegs_ne p hp
    rw [g₂ _ n5, g₁ _ n5 n10]
  obtain ⟨s₃, h₃, a₃, k₃, hm₃, v₃, m₃, rd₃, wr₃, sp₃⟩ := pOut_ok s₂ hab hm₂
  have hc₃ : Consts s₃ := hc₂.congr fun w _ _ _ _ => by rw [v₃]
  have a₂ : s₂.gpr a = spreadW l := by rw [g₂ a ha5, g₁ a ha5 ha10, hl]
  -- The S-boxes' outputs.
  have hy : ∀ l' < 8, (s₂.gpr .x5).extractLsb' (8 * l') 8 = sTable (I l').toNat := by
    intro l' hl'
    rw [y₂ l' hl', hc₁.tab _ (I l').isLt]
  have hI : ∀ i < 8, (I (laneOf i)).toNat = 2 ^ 6 * boxTable i + (chunk r (K.setWidth 48) i).toNat := by
    intro i hi
    have hL := laneOf_lt i hi
    simp only [I]
    rw [i₀ _ hL, hK, hr, index_byte K r hL, boxOf_laneOf i hi, BitVec.toNat_ofNat]
    have := (chunk r (K.setWidth 48) i).isLt
    have := tableOf_lt i hi
    omega_arith
  refine ⟨s₃, ?_, ?_, ?_, fun g hg => ?_, hc₃, hm₃, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], by rw [sp₃, sp₂, sp₁]⟩
  · rw [round, runBlock_cat_some (runBlock_cat_some h₁ h₂) h₃]
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [a₃ p hp, a₂, getLsbD_spreadW _ hp, getLsbD_spreadW _ hp]
    have hj := xSrc_rot_lt p hp
    cases hx : xBit p
    · have : ySrc p = none := by simp [ySrc, hx]
      rw [this]; simp
    · rw [ySrc_eq hx, BitVec.getLsbD_xor, Bool.true_and, Bool.true_and,
        getLsbD_roundFunction r _ hj]
      dsimp only
      have hu := pSrc_lt _ hj
      have hi : 7 - pSrc ((xSrc p + 32 - rot) % 32) / 4 < 8 := by omega_arith
      have hq : pSrc ((xSrc p + 32 - rot) % 32) % 4 < 4 := Nat.mod_lt _ (by decide)
      rw [y_bit I sTable hy hi (posOf_lt _ hi _ hq), hI _ hi,
        sTable_bit _ hi _ (chunk r (K.setWidth 48) _).isLt _ hq, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, Bool.xor_comm]
  · rw [k₃ .x10 (by simp [pKept]), g₂ .x10 (by decide), x10₁]
  · have hg' : g ∈ b :: pKept := by
      simp only [pKept, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
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

end


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

@[expose] public section

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

theorem eval_nonzero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x r) s = some !decide (x = 0) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hx]

theorem eval_zero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.zero .x r) s = some (decide (x = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all


/-- What the block needs: the key schedule at `x14` readable, and the first
456 bytes of the scratch buffer at `x15` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ R ∈ s.rd ++ s.wr, R.base = s.gpr .x14 ∧ 384 ≤ R.len ∧ R.len < 2 ^ 64
  scr : ∃ R ∈ s.wr, R.base = s.gpr .x15 ∧ 456 ≤ R.len ∧ R.len < 2 ^ 64
  disj : Region.Disjoint ⟨s.gpr .x15, 456⟩ ⟨s.gpr .x14, 384⟩

/-- The spread round keys' slots. -/
abbrev xR (s₀ : State) : Region := ⟨s₀.gpr .x15, 384⟩

/-- The registers of the functions that the block keeps (with `x14` and `x15`). -/
def outer : List Reg := [.x1, .x2, .x3, .x4]

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  x15 : s.gpr .x15 = s₀.gpr .x15
  keep : ∀ r ∈ outer, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [xR s₀] s₀.mem s.mem

theorem Same.refl (s : State) : Same s s := ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x14)

/-- The spread round keys, in the scratch buffer. -/
def Keys (s₀ : State) (m : Mem) (n : Nat) : Prop :=
  ∀ i < n, m.readW (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 64 = spread ((sch s₀).getD i 0)

theorem BlockPre.slot {s₀ : State} (hp : BlockPre s₀) {s : State} (h : Same s₀ s) {d n : Nat}
    (hd : d + n ≤ 384) : InRegions s.wr (s₀.gpr .x15 + BitVec.ofNat 64 d) n := by
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  rw [h.wr]
  exact ⟨X, hX, by rw [← hXb]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem BlockPre.key {s₀ : State} (hp : BlockPre s₀) {s : State} (h : Same s₀ s) {d n : Nat}
    (hd : d + n ≤ 384) : InRegions (s.rd ++ s.wr) (s₀.gpr .x14 + BitVec.ofNat 64 d) n := by
  obtain ⟨R, hR, hRb, hRl, hRw⟩ := hp.sched
  rw [h.rd, h.wr]
  exact ⟨R, hR, by rw [← hRb]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The key schedule is unchanged while only the scratch buffer changes. -/
theorem sched_word {s₀ : State} (hp : BlockPre s₀) {m : Mem} (hf : Frame [xR s₀] s₀.mem m) {d : Nat}
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
  omega_arith

/-! ## Memory -/

theorem vdword_read (m : Mem) (a : Addr) {h : Nat} (hh : h < 2) :
    vdword (m.read a 16) h = m.readW (a + BitVec.ofNat 64 (8 * h)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_vdword _ hi, getLsbD_read m 16 a _ (by omega_arith), getLsbD_readW64 _ _ hi,
    BitVec.add_assoc, ← BitVec.ofNat_add, show (64 * h + i) / 8 = 8 * h + i / 8 by omega_arith,
    show (64 * h + i) % 8 = i % 8 by omega_arith]

theorem readW_write16 (m : Mem) (a : Addr) (v : BitVec 128) {h : Nat} (hh : h < 2) :
    (m.write a 16 v).readW (a + BitVec.ofNat 64 (8 * h)) 64 = vdword v h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_readW64 _ _ hi, getLsbD_vdword _ hi, BitVec.add_assoc, ← BitVec.ofNat_add, Mem.write,
    Mem.sub_ofNat_toNat a (by omega_arith), ite_eq_left (by omega_arith)]
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega_arith, decide_true, Bool.true_and]
  congr 1; omega_arith

/-! ## Spreading the round keys -/

theorem exec_mov {s : State} {d n : Reg} : exec (mov d n) s = some (s.write .x d (s.gpr n)) := by
  rw [mov, exec_addImm_x (by decide)]
  simp [State.read]

theorem exec_movz_x {s : State} {d : Reg} {imm : BitVec 16} {hw : Nat} (h : hw < 4) :
    exec (.movz .x d imm hw) s = some (s.write .x d (imm.setWidth 64 <<< (16 * hw))) := by
  simp only [exec, Size.bits, show 16 * hw < 64 by omega_arith, ite_true]

theorem exec_dupd (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

/-- After `m` pairs of keys. -/
structure SInv (s₀ : State) (m : Nat) (s : State) : Prop where
  same : Same s₀ s
  x5 : s.gpr .x5 = s₀.gpr .x5
  x14 : s.gpr .x14 = s₀.gpr .x14
  x6 : s.gpr .x6 = s₀.gpr .x14 + BitVec.ofNat 64 (16 * m)
  x7 : s.gpr .x7 = s₀.gpr .x15 + BitVec.ofNat 64 (16 * m)
  x16 : s.gpr .x16 = BitVec.ofNat 64 (24 - m)
  g : s.v .v5 = ofVBytes gatherIndex
  c63 : s.v .v6 = bc 63
  off : s.v .v7 = ofVDwords offsets offsets
  keys : Keys s₀ s.mem (2 * m)

theorem spreadPre_eq : spreadPre = const128 .v5 (ofVBytes gatherIndex) ++
    (([.movz .x .x6 63 0, .vop (.dup .b16 .v6 .x6)] : List Instr) ++ (const64 .x6 offsets ++
      ([.vop (.dup .d2 .v7 .x6), mov .x6 .x14, mov .x7 .x15, .movz .x .x16 24 0] : List Instr))) := by
  simp only [spreadPre, List.append_assoc]

theorem spreadPre_ok (s₀ : State) : WP isa (.block spreadPre) s₀ (SInv s₀ 0) := by
  rw [spreadPre_eq, WP.block_append_iff]
  refine WP.mono (const128_ok s₀ .v5 _) fun a ⟨a5, av, ag, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  let b := (a.write .x .x6 ((63 : BitVec 16).setWidth 64 <<< (16 * 0)))
  let b' := b.setV .v6 (bc ((b.gpr .x6).setWidth 8))
  refine WP.of_runBlock ⟨b', by
    rw [runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_cons, exec_dupb, runStep_some,
      runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b' .x6 offsets) fun c ⟨c6, cg, ce⟩ => ?_
  let d₁ := c.setV .v7 (ofVDwords (c.gpr .x6) (c.gpr .x6))
  let d₂ := d₁.write .x .x6 (d₁.gpr .x14)
  let d₃ := d₂.write .x .x7 (d₂.gpr .x15)
  let d₄ := d₃.write .x .x16 ((24 : BitVec 16).setWidth 64 <<< (16 * 0))
  refine WP.of_runBlock ⟨d₄, by
    rw [runBlock_cons, exec_dupd, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_cons,
      exec_mov, runStep_some, runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have cv : c.v = b'.v := by rw [ce]
  have cmem : c.mem = s₀.mem := by rw [ce]; exact am
  have g14 : c.gpr .x14 = s₀.gpr .x14 := by
    rw [cg .x14 (by decide)]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x6)]
    exact ag .x14 (by decide) (by decide)
  have g15 : c.gpr .x15 = s₀.gpr .x15 := by
    rw [cg .x15 (by decide)]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x6)]
    exact ag .x15 (by decide) (by decide)
  have gout : ∀ r ∈ outer, c.gpr r = s₀.gpr r := by
    intro r hr
    have h6 : r ≠ .x6 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h7 : r ≠ .x7 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [cg r h6]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ h6]; exact ag r h6 h7
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith)⟩
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x7), gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x6),
      gpr_setV, g15]
  · have h6 : r ≠ .x6 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h7 : r ≠ .x7 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h16 : r ≠ .x16 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
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

theorem spreadBody_eq : spreadBody = ([.ldrq .v0 .x6 0] : List Instr) ++ spreadV ++
    ([.strq .v4 .x7 0, .addImm .x .x6 .x6 16, .addImm .x .x7 .x7 16, .subImm .x .x16 .x16 1] : List Instr) :=
  rfl

theorem exec_ldrq0 (s : State) (t : VReg) (n : Reg) (h : InRegions (s.rd ++ s.wr) (s.gpr n) 16) :
    exec (.ldrq t n 0) s = some (s.setV t (s.mem.read (s.gpr n) 16)) := by
  simp only [exec, addr, show 0 % 16 = 0 from rfl, show 0 < 4096 * 16 by decide, and_self, ite_true,
    BitVec.add_zero, Option.bind_some, State.load, h, Option.map_some]

theorem exec_strq0 (s : State) (t : VReg) (n : Reg) (h : InRegions s.wr (s.gpr n) 16) :
    exec (.strq t n 0) s = some { s with mem := s.mem.write (s.gpr n) 16 (s.v t) } := by
  simp only [exec, addr, show 0 % 16 = 0 from rfl, show 0 < 4096 * 16 by decide, and_self, ite_true,
    BitVec.add_zero, Option.bind_some, State.store, h]

theorem spreadStep_ok {s₀ : State} (hp : BlockPre s₀) {m : Nat} (hm : m < 24) {s : State}
    (h : SInv s₀ m s) : WP isa (.block spreadBody) s (SInv s₀ (m + 1)) := by
  rw [spreadBody_eq, WP.block_append_iff, WP.block_append_iff]
  have rk : InRegions (s.rd ++ s.wr) (s.gpr .x6) 16 := by
    rw [h.x6]; exact hp.key h.same (by omega_arith)
  let s₁ := s.setV .v0 (s.mem.read (s.gpr .x6) 16)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_ldrq0 _ _ _ rk, runStep_some, runBlock_nil], ?_⟩
  obtain ⟨s₂, h₂, v4₂, v₂, e₂⟩ := spreadV_ok s₁
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
    rw [wr₂, g₂, h.x7]; exact hp.slot h.same (by omega_arith)
  let V := s₂.v .v4
  let s₃ : State := { s₂ with mem := s₂.mem.write (s₂.gpr .x7) 16 V }
  let s₄ := s₃.write .x .x6 (s₃.read .x .x6 + BitVec.ofNat _ 16)
  let s₅ := s₄.write .x .x7 (s₄.read .x .x7 + BitVec.ofNat _ 16)
  let s₆ := s₅.write .x .x16 (s₅.read .x .x16 - BitVec.ofNat _ 1)
  refine WP.of_runBlock ⟨s₆, by
    rw [runBlock_cons, exec_strq0 _ _ _ ws, runStep_some, runBlock_cons, exec_addImm_x (by decide),
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
  have hK : ∀ hh < 2, vdword (s₁.v .v0) hh = (sch s₀).getD (2 * m + hh) 0 := by
    intro hh hh2
    rw [show s₁.v .v0 = s.mem.read (s.gpr .x6) 16 from v_setV_self _ _ _, vdword_read _ _ hh2, h.x6,
      Offset.add_add, scheduleAt_getD _ _ (by omega_arith),
      show 16 * m + 8 * hh = 8 * (2 * m + hh) by omega_arith]
    exact sched_word hp h.same.frame (by omega_arith)
  have outer_ne : ∀ r ∈ outer, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x16 := by
    intro r hr; simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₆ _ (by decide) (by decide) (by decide), h.same.x15]
  · obtain ⟨a, b, c⟩ := outer_ne r hr
    rw [g₆ r a b c, h.same.keep r hr]
  · show s₂.sp = _; rw [sp₂, h.same.sp]
  · show s₂.rd = _; rw [rd₂, h.same.rd]
  · show s₂.wr = _; rw [wr₂, h.same.wr]
  · rw [mem₆]
    exact h.same.frame.write (r := xR s₀) (by simp) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · rw [g₆ _ (by decide) (by decide) (by decide), h.x5]
  · rw [g₆ _ (by decide) (by decide) (by decide), h.x14]
  · simp only [s₆, s₅, s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x7), gpr_write_self, State.read,
      BitVec.setWidth_eq]
    show s₂.gpr .x6 + _ = _
    rw [g₂, h.x6, Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
  · simp only [s₆, s₅, gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x16), gpr_write_self, State.read,
      BitVec.setWidth_eq, s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x6)]
    show s₂.gpr .x7 + _ = _
    rw [g₂, h.x7, Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
  · simp only [s₆, gpr_write_self, State.read, BitVec.setWidth_eq, s₅,
      gpr_write_of_ne _ _ _ (by decide : Reg.x16 ≠ .x7), s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x16 ≠ .x6)]
    show s₂.gpr .x16 - _ = _
    rw [g₂, h.x16]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Size.bits]
    omega_arith
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v0), h.g]
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v0), h.c63]
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v0), h.off]
  · intro i hi
    rw [mem₆]
    by_cases hnew : 2 * m ≤ i
    · have hh : i - 2 * m < 2 := by omega_arith
      rw [show s₀.gpr .x15 + BitVec.ofNat 64 (8 * i) =
          s₀.gpr .x15 + BitVec.ofNat 64 (16 * m) + BitVec.ofNat 64 (8 * (i - 2 * m)) by
          rw [Offset.add_add]; congr 2; omega_arith,
        readW_write16 _ _ _ hh]
      show vdword (s₂.v .v4) _ = _
      have hK' : vdword (s₁.v .v0) (i - 2 * m) = (sch s₀).getD i 0 := by
        rw [hK _ hh, show 2 * m + (i - 2 * m) = i by omega_arith]
      rw [v4₂, ← hK']
      rcases (by omega_arith : i - 2 * m = 0 ∨ i - 2 * m = 1) with e | e <;> rw [e]
      · rw [vdword_ofVDwords_0]
      · rw [vdword_ofVDwords_1]
    · have hsep : Mem.Sep (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 8
          (s₀.gpr .x15 + BitVec.ofNat 64 (16 * m)) 16 :=
        Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)
      rw [Mem.readW, Mem.read_write_sep hsep (by decide)]
      exact h.keys i (by omega_arith)

theorem spreadLoop_ok {s₀ : State} (hp : BlockPre s₀) {s : State} (h : SInv s₀ 0 s) :
    WP isa (.loop (.block spreadBody) (.nonzero .x .x16)) s (SInv s₀ 24) := by
  refine WP.loop (M := isa) (body := .block spreadBody) (c := .nonzero .x .x16) (Q := SInv s₀ 24)
    (fun (n : Nat) (t : State) => ∃ m, n = 24 - m ∧ m < 24 ∧ SInv s₀ m t) ?_ 24 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨m, rfl, hm, ht⟩
  refine WP.mono (spreadStep_ok hp hm ht) fun t' h' => ?_
  have ev := eval_nonzero (r := .x16) (x := 24 - (m + 1)) (by omega_arith) h'.x16
  by_cases hz : m + 1 = 24
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega_arith, 24 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- No memory. -/
theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

/-- `IP`'s halves, rotated and spread, into `x11` and `x12`, from `x5` (input word 0). -/
def ipG11 (p : Nat) : List Nat := if xBit p then [ipSrc (32 + (xSrc p + 32 - rot) % 32)] else []
def ipG12 (p : Nat) : List Nat := if xBit p then [ipSrc ((xSrc p + 32 - rot) % 32)] else []

theorem ip_check :
    check (lanes 64 6) oCfg (linExt 1) ipCode (linEnv [(.x5, 0)])
      (linPost 6 [(.x11, ipG11), (.x12, ipG12)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into `x5`, from `R` spread in `x12` (input word 0) and `L`
spread in `x11` (input word 1). -/
def fpG (j : Nat) : List Nat :=
  if 32 ≤ fpSrc j then [xPos ((fpSrc j - 32 + rot) % 32)] else [64 + xPos ((fpSrc j + rot) % 32)]

theorem fp_check :
    check (lanes 64 7) oCfg (linExt 2) fpCode (linEnv [(.x12, 0), (.x11, 1)]) (linPost 7 [(.x5, fpG)]) = true := by
  lit_decide

def blockKept : List Reg := [.x1, .x2, .x3, .x4, .x10, .x14, .x15]

theorem ip_kept : blockKept.all (fun r => ipCode.all fun i => !clobbers i r) = true := by lit_decide

theorem fp_kept : blockKept.all (fun r => fpCode.all fun i => !clobbers i r) = true := by lit_decide

theorem fp_v : fpCode.all (fun i => vdstOf i == none) = true := by lit_decide

theorem fp_masks : maskConsts.all (fun p => fpCode.all fun i => !clobbers i p.1) = true := by
  lit_decide

theorem ip_v : ipCode.all (fun i => vdstOf i == none) = true := by lit_decide

theorem ip_masks : maskConsts.all (fun p => ipCode.all fun i => !clobbers i p.1) = true := by
  lit_decide

theorem xPos_facts : ∀ e < 32, xPos e < 64 ∧ xBit (xPos e) = true ∧ xSrc (xPos e) = e := by decide

theorem ip_ok (s : State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      s'.gpr .x11 = spreadW (split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x5))).1 ∧
      s'.gpr .x12 = spreadW (split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x5))).2 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.v = s.v ∧ (∀ p ∈ maskConsts, s'.gpr p.1 = s.gpr p.1) := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok ip_check (oCfg_ok s) (fun _ => s.gpr .x5)
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, ?_, hrd, hwr, hsp, fun r hr => hoth r (List.all_eq_true.mp ip_kept r hr),
    frame_oCfg hfr, runBlock_v ip_v hs', fun p hp => hoth p.1 (List.all_eq_true.mp ip_masks p hp)⟩
  · apply BitVec.eq_of_getLsbD_eq; intro p hp
    have hj := xSrc_rot_lt p hp
    rw [hout .x11 ipG11 (by simp) p hp, getLsbD_spreadW _ hp, ipG11]
    cases hx : xBit p
    · simp
    · have hs := ipSrc_lt (32 + (xSrc p + 32 - rot) % 32) (by omega_arith)
      simp only [ite_true, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs,
        Bool.true_and, split, BitVec.getLsbD_setWidth, decide_eq_true hj,
        BitVec.getLsbD_ushiftRight]
      rw [getLsbD_permute _ _ (by decide) (show 32 + (xSrc p + 32 - rot) % 32 < 64 by omega_arith)]
      rfl
  · apply BitVec.eq_of_getLsbD_eq; intro p hp
    have hj := xSrc_rot_lt p hp
    rw [hout .x12 ipG12 (by simp) p hp, getLsbD_spreadW _ hp, ipG12]
    cases hx : xBit p
    · simp
    · have hs := ipSrc_lt ((xSrc p + 32 - rot) % 32) (by omega_arith)
      simp only [ite_true, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs,
        Bool.true_and, split, BitVec.getLsbD_setWidth, decide_eq_true hj]
      rw [getLsbD_permute _ _ (by decide) (show (xSrc p + 32 - rot) % 32 < 64 by omega_arith)]
      rfl

theorem spreadW_xPos (w : BitVec 32) {k : Nat} (hk : k < 32) :
    (spreadW w).getLsbD (xPos ((k + rot) % 32)) = w.getLsbD k := by
  obtain ⟨h64, hx, hs⟩ := xPos_facts ((k + rot) % 32) (by omega_arith)
  rw [getLsbD_spreadW _ h64, hx, hs, Bool.true_and]
  congr 1; simp only [rot]; omega_arith

theorem fp_ok (s : State) {l r : BitVec 32} (hl : s.gpr .x11 = spreadW l) (hr : s.gpr .x12 = spreadW r) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      s'.gpr .x5 = Spec.TripleDes.permute Spec.TripleDes.fp (r ++ l) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.v = s.v ∧ (∀ p ∈ maskConsts, s'.gpr p.1 = s.gpr p.1) := by
  let W : Nat → BitVec 64 := fun i => if i = 0 then s.gpr .x12 else s.gpr .x11
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok fp_check (oCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, fun r hr => hoth r (List.all_eq_true.mp fp_kept r hr), frame_oCfg hfr,
    runBlock_v fp_v hs', fun p hp => hoth p.1 (List.all_eq_true.mp fp_masks p hp)⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hs := fpSrc_lt j hj
  rw [hout .x5 fpG (by simp) j hj, getLsbD_permute _ _ (by decide) hj, BitVec.getLsbD_append,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl, fpG]
  by_cases h32 : 32 ≤ fpSrc j
  · obtain ⟨h64, -, -⟩ := xPos_facts ((fpSrc j - 32 + rot) % 32) (by omega_arith)
    rw [ite_eq_left h32, ite_eq_right (by omega_arith)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.div_eq_of_lt h64,
      Nat.mod_eq_of_lt h64, W, ite_true, hr]
    exact spreadW_xPos r (by omega_arith)
  · obtain ⟨h64, -, -⟩ := xPos_facts ((fpSrc j + rot) % 32) (by omega_arith)
    rw [ite_eq_right h32, ite_eq_left (by omega_arith)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      show (64 + xPos ((fpSrc j + rot) % 32)) / 64 = 1 by omega_arith,
      show (64 + xPos ((fpSrc j + rot) % 32)) % 64 = xPos ((fpSrc j + rot) % 32) by omega_arith, W,
      show (1 : Nat) ≠ 0 by decide, ite_false, hl]
    exact spreadW_xPos l (by omega_arith)

/-! ## The setup -/

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : kpos p j < 48 := by
  simp only [kpos]; split <;> omega_arith

/-- The slot of the schedule that the passes take as slot `i`: the same for
encryption, and for decryption (`rv`) the slots in reverse, since
`D_K1(E_K2(D_K3(x)))` is `E`, `D`, `E` with the 48 round keys in reverse. -/
def slotOf (rv : Bool) (i : Nat) : Nat := if rv then 47 - i else i

/-- The schedule the passes run. -/
def schOf (rv : Bool) (s₀ : State) : Spec.TripleDes.Schedule := revIf rv (sch s₀)

theorem slotOf_lt (rv : Bool) {i : Nat} (hi : i < 48) : slotOf rv i < 48 := by
  unfold slotOf; split <;> omega_arith

theorem schOf_getD (rv : Bool) (s₀ : State) {i : Nat} (hi : i < 48) :
    (schOf rv s₀).getD i 0 = (sch s₀).getD (slotOf rv i) 0 := by
  cases rv
  · rfl
  · exact revIf_getD _ hi

/-- Before pass `p`, from the block `x`. -/
structure OInv (rv : Bool) (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : Same s₀ s
  x14 : s.gpr .x14 = s₀.gpr .x14
  x10 : s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * slotOf rv (kpos p 0))
  consts : Consts s
  masks : Masks s
  keys : Keys s₀ s.mem 48
  l : s.gpr .x11 = spreadW (passes (schOf rv s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))).1
  r : s.gpr .x12 = spreadW (passes (schOf rv s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))).2

theorem quarterConsts_ok (s : State) :
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
    check (lanes 64 7) oCfg (linExt 2) maskSet (linEnv [])
      (fun e => maskConsts.all fun p => e.cst p.1 == some p.2) = true := by
  lit_decide

/-- The registers the masks' setup keeps. -/
def maskKept : List Reg := [.x1, .x2, .x3, .x4, .x5, .x14, .x15]

theorem maskSet_keeps : maskKept.all (fun r => maskSet.all fun i => !clobbers i r) = true := by
  lit_decide

theorem maskSet_v : maskSet.all (fun i => vdstOf i == none) = true := by lit_decide

theorem maskSet_ok (s : State) :
    ∃ s', runBlock isa maskSet s = some s' ∧ Masks s' ∧ (∀ r ∈ maskKept, s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ maskSet_check
  have hrel : Rel (LaneRel 7 0) oCfg (linExt 2) (linEnv []) s :=
    ⟨fun r a h => (by simp [linEnv] at h), fun _ _ _ h => (by cases h),
      fun j _ hj _ => absurd hj (by simp [oCfg]), fun _ _ h => (by cases h)⟩
  obtain ⟨s', hs', p⟩ := run lanes_sound (oCfg_ok s) hrel he
  refine ⟨s', hs', fun r v hp => p.rel.cst r v ?_, fun r hr => p.other r fun h => ?_,
    runBlock_v maskSet_v hs', frame_oCfg p.frame, p.rd, p.wr, p.sp⟩
  · have := List.all_eq_true.mp hpost (r, v) hp
    simpa using this
  · rw [List.all_eq_true.mp maskSet_keeps r hr] at h; cases h

/-- After the setup shared by the blocks of one call: the tables, constants,
masks and spread keys, and the block `x5` as it was. -/
structure TInv (s₀ s : State) : Prop where
  same : Same s₀ s
  x5 : s.gpr .x5 = s₀.gpr .x5
  x14 : s.gpr .x14 = s₀.gpr .x14
  consts : Consts s
  masks : Masks s
  keys : Keys s₀ s.mem 48

theorem tables_eq : tables = loadTable sTable ++ (quarterConsts ++ maskSet) := by
  simp only [tables, List.append_assoc]

theorem tables_ok {s₀ : State} {s : State} (h : SInv s₀ 24 s) :
    WP isa (.block tables) s (TInv s₀) := by
  rw [tables_eq, WP.block_append_iff]
  refine WP.mono (loadTable_ok s sTable) fun a ⟨atab, av, ag, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  obtain ⟨b₀, hb, b4, b5, b6, bv₀, bg₀, bm₀, brd₀, bwr₀, bsp₀⟩ := quarterConsts_ok a
  refine WP.of_runBlock ⟨b₀, hb, ?_⟩
  obtain ⟨b, hbm, bmask, bk, bvv, bm₁, brd₁, bwr₁, bsp₁⟩ := maskSet_ok b₀
  refine WP.of_runBlock ⟨b, hbm, ?_⟩
  have bv : ∀ w, w ≠ .v4 → w ≠ .v5 → w ≠ .v6 → b.v w = a.v w := fun w h4 h5 h6 => by
    rw [bvv]; exact bv₀ w h4 h5 h6
  have g : ∀ r ∈ maskKept, r ≠ .x6 → r ≠ .x7 → b.gpr r = s.gpr r := fun r hr h6 h7 => by
    rw [bk r hr, bg₀ r h6, ag r h6 h7]
  have bm : b.mem = s.mem := by rw [bm₁, bm₀, am]
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨fun k hk => ?_, ?_, ?_, ?_⟩, bmask, ?_⟩
  · rw [g _ (by simp [maskKept]) (by decide) (by decide), h.same.x15]
  · have hm : r ∈ maskKept ∧ r ≠ .x6 ∧ r ≠ .x7 := by
      simp only [outer, maskKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [g r hm.1 hm.2.1 hm.2.2, h.same.keep r hr]
  · rw [bsp₁, bsp₀, asp, h.same.sp]
  · rw [brd₁, brd₀, ard, h.same.rd]
  · rw [bwr₁, bwr₀, awr, h.same.wr]
  · rw [bm]; exact h.same.frame
  · rw [g _ (by simp [maskKept]) (by decide) (by decide), h.x5]
  · rw [g _ (by simp [maskKept]) (by decide) (by decide), h.x14]
  · rw [tbyte_congr' (fun t ht => ?_) k hk, atab k hk]
    obtain ⟨-, -, -, -, h4, h5, h6, -⟩ := treg_ne8 t ht
    exact bv _ h4 h5 h6
  · rw [bvv]; exact b4
  · rw [bvv]; exact b5
  · rw [bvv]; exact b6
  · rw [bm]; exact h.keys

/-- `IP`, and `x10` to the first spread key: before the first pass. -/
theorem encStart_ok (rv : Bool) {s₀ : State} {s : State} (h : TInv s₀ s) :
    WP isa (.block (ipCode ++ ([.addImm .x .x10 .x15 (8 * slotOf rv 0)] : List Instr))) s
      (OInv rv s₀ (s₀.gpr .x5) 0) := by
  rw [WP.block_append_iff]
  obtain ⟨c, hc, c11, c12, crd, cwr, csp, ck, cm, cv, cmask⟩ := ip_ok s
  refine WP.of_runBlock ⟨c, hc, ?_⟩
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_addImm_x (by cases rv <;> decide), runStep_some, runBlock_nil], ?_⟩
  have x15c : c.gpr .x15 = s₀.gpr .x15 := by rw [ck .x15 (by simp [blockKept]), h.same.x15]
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.consts.congr (fun w _ _ _ _ => by rw [v_write, cv]),
    ?_, ?_, ?_, ?_⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), x15c]
  · have hk : r ∈ blockKept ∧ r ≠ .x10 := by
      simp only [outer, blockKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [gpr_write_of_ne _ _ _ hk.2, ck r hk.1, h.same.keep r hr]
  · rw [sp_write, csp, h.same.sp]
  · rw [rd_write, crd, h.same.rd]
  · rw [wr_write, cwr, h.same.wr]
  · rw [mem_write, cm]; exact h.same.frame
  · rw [gpr_write_of_ne _ _ _ (by decide), ck .x14 (by simp [blockKept]), h.x14]
  · rw [gpr_write_self, BitVec.setWidth_eq, State.read, BitVec.setWidth_eq, x15c]
    rfl
  · exact h.masks.congr fun p hp => by
      rw [gpr_write_of_ne _ _ _ (maskRegs_ne p hp).2.1, cmask p hp]
  · rw [mem_write, cm]
    exact h.keys
  · rw [gpr_write_of_ne _ _ _ (by decide), c11, h.x5]
    rfl
  · rw [gpr_write_of_ne _ _ _ (by decide), c12, h.x5]
    rfl

/-! ## The passes -/

/-- After `j` pairs of rounds of pass `p`, from the halves `lr`. -/
structure PInv (rv : Bool) (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) :
    Prop where
  same : Same s₀ s
  x14 : s.gpr .x14 = s₀.gpr .x14
  x10 : j < 8 ∨ p < 2 ∨ rv = false →
    s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * slotOf rv (kpos p (2 * j)))
  x16 : s.gpr .x16 = BitVec.ofNat 64 (8 - j)
  consts : Consts s
  masks : Masks s
  keys : Keys s₀ s.mem 48
  l : s.gpr .x11 = spreadW (rounds (passKeys (schOf rv s₀) p) (2 * j) lr).1
  r : s.gpr .x12 = spreadW (rounds (passKeys (schOf rv s₀) p) (2 * j) lr).2

/-- The pass moves down the keys. -/
def downOf (p : Nat) : Bool := p % 2 == 1

theorem kpos_step (rv : Bool) (a : Addr) {p i : Nat} (hp : p < 3) (hi : i < 16)
    (hs : i < 15 ∨ p < 2 ∨ rv = false) :
    (if (downOf p != rv) then a + BitVec.ofNat 64 (8 * slotOf rv (kpos p i)) - 8
      else a + BitVec.ofNat 64 (8 * slotOf rv (kpos p i)) + 8) =
      a + BitVec.ofNat 64 (8 * slotOf rv (kpos p (i + 1))) := by
  have hc : p = 0 ∨ p = 1 ∨ p = 2 := by omega_arith
  have h15 : rv = true → p = 2 → i < 15 := fun h1 h2 => by
    rcases hs with h | h | h
    · exact h
    · omega_arith
    · rw [h1] at h; cases h
  cases rv <;> rcases hc with rfl | rfl | rfl <;>
    simp only [downOf, kpos, slotOf, Nat.reduceMod, Nat.reduceBEq, ↓reduceIte,
      bne_self_eq_false, Bool.false_eq_true, Bool.true_bne, Bool.false_bne, Bool.not_false,
      reduceCtorEq] <;>
    (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
     first
       | omega_arith
       | (have := h15 rfl rfl; omega_arith))

theorem passKeys_at (rv : Bool) (s₀ : State) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    passKeys (schOf rv s₀) p j = ((sch s₀).getD (slotOf rv (kpos p j)) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega_arith,
      schOf_getD _ _ (by omega_arith)]
  · rw [ite_eq_right h, ite_eq_right h, schOf_getD _ _ (by omega_arith)]

theorem outer_ne {r : Reg} (h : r ∈ outer) :
    r ≠ .x5 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x16 := by
  simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem pairBody_eq (down : Bool) :
    (round .x11 .x12 down ++ round .x12 .x11 down ++ ([.subImm .x .x16 .x16 1] : List Instr)) =
      round .x11 .x12 down ++ (round .x12 .x11 down ++ ([.subImm .x .x16 .x16 1] : List Instr)) := by
  simp only [List.append_assoc]

/-- Two rounds of pass `p`. -/
theorem pairStep_ok (rv : Bool) {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3)
    {lr : BitVec 32 × BitVec 32} {j : Nat} (hj : j < 8) {s : State} (h : PInv rv s₀ p lr j s) :
    WP isa (.block (round .x11 .x12 (downOf p != rv) ++ round .x12 .x11 (downOf p != rv) ++
      ([.subImm .x .x16 .x16 1] : List Instr))) s (PInv rv s₀ p lr (j + 1)) := by
  rw [pairBody_eq, WP.block_append_iff]
  have slot : ∀ {t : State}, Same s₀ t → ∀ i < 48,
      InRegions (t.rd ++ t.wr) (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro t ht i hi
    obtain ⟨R, hR, hc⟩ := hp.slot ht (d := 8 * i) (n := 8) (by omega_arith)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have k0 := slotOf_lt rv (kpos_lt hp3 (show 2 * j < 16 by omega_arith))
  have k1 := slotOf_lt rv (kpos_lt hp3 (show 2 * j + 1 < 16 by omega_arith))
  have hx10 := h.x10 (Or.inl hj)
  obtain ⟨s₁, h₁, a₁, x10₁, g₁, c₁, mk₁, m₁, rd₁, wr₁, sp₁⟩ := round_ok (Or.inl ⟨rfl, rfl⟩) (downOf p != rv)
    h.consts h.masks (by rw [hx10]; exact slot h.same _ k0) h.l h.r
    (by rw [hx10]; exact h.keys _ k0)
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  rw [WP.block_append_iff]
  have same₁ : Same s₀ s₁ := ⟨by rw [g₁ .x15 (by simp), h.same.x15],
    fun r hr => by rw [g₁ r (by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> simp), h.same.keep r hr],
    by rw [sp₁, h.same.sp], by rw [rd₁, h.same.rd], by rw [wr₁, h.same.wr], by rw [m₁]; exact h.same.frame⟩
  have x10₁' : s₁.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * slotOf rv (kpos p (2 * j + 1))) := by
    rw [x10₁, hx10, kpos_step rv _ hp3 (by omega_arith) (Or.inl (by omega_arith))]
  obtain ⟨s₂, h₂, a₂, x10₂, g₂, c₂, mk₂, m₂, rd₂, wr₂, sp₂⟩ := round_ok (Or.inr ⟨rfl, rfl⟩) (downOf p != rv)
    c₁ mk₁ (by rw [x10₁']; exact slot same₁ _ k1) (by rw [g₁ .x12 (by simp), h.r]) a₁
    (by rw [x10₁', m₁]; exact h.keys _ k1)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have hr₁ := rounds_succ (passKeys (schOf rv s₀) p) (2 * j) lr
  have hr₂ := rounds_succ (passKeys (schOf rv s₀) p) (2 * j + 1) lr
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x15 (by simp), same₁.x15]
  · rw [gpr_write_of_ne _ _ _ (outer_ne hr).2.2.2.2, g₂ r (by
      simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), same₁.keep r hr]
  · rw [sp_write, sp₂, same₁.sp]
  · rw [rd_write, rd₂, same₁.rd]
  · rw [wr_write, wr₂, same₁.wr]
  · rw [mem_write, m₂]; exact same₁.frame
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x14 (by simp), g₁ .x14 (by simp), h.x14]
  · intro hs
    rw [gpr_write_of_ne _ _ _ (by decide), x10₂, x10₁',
      kpos_step rv _ hp3 (by omega_arith) (hs.imp (fun h => by omega_arith) id),
      show 2 * (j + 1) = 2 * j + 1 + 1 by omega_arith]
  · rw [gpr_write_self, State.read, BitVec.setWidth_eq, BitVec.setWidth_eq, g₂ .x16 (by simp),
      g₁ .x16 (by simp), h.x16]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Size.bits]
    omega_arith
  · exact c₂.congr fun _ _ _ _ _ => rfl
  · exact mk₂.congr fun p hp => gpr_write_of_ne _ _ _ (maskRegs_ne p hp).2.2.2.2.1
  · rw [mem_write, m₂, m₁]; exact h.keys
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x11 (by simp), a₁, show 2 * (j + 1) = 2 * j + 1 + 1 by omega_arith,
      hr₂, hr₁, passKeys_at rv s₀ hp3 (show 2 * j < 16 by omega_arith)]
  · rw [gpr_write_of_ne _ _ _ (by decide), a₂, show 2 * (j + 1) = 2 * j + 1 + 1 by omega_arith, hr₂, hr₁,
      passKeys_at rv s₀ hp3 (show 2 * j < 16 by omega_arith),
      passKeys_at rv s₀ hp3 (show 2 * j + 1 < 16 by omega_arith)]

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok (rv : Bool) {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3)
    {lr : BitVec 32 × BitVec 32}
    {s : State} (h : Same s₀ s) (h14 : s.gpr .x14 = s₀.gpr .x14)
    (h10 : s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * slotOf rv (kpos p 0))) (hc : Consts s)
    (hm : Masks s)
    (hk : Keys s₀ s.mem 48) (hl : s.gpr .x11 = spreadW lr.1) (hr : s.gpr .x12 = spreadW lr.2) :
    WP isa (pass (downOf p != rv)) s (PInv rv s₀ p lr 8) := by
  refine WP.seq (WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have g : ∀ r, r ≠ .x16 → (s.write .x .x16 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))).gpr r = s.gpr r :=
    fun r hr => gpr_write_of_ne _ _ _ hr
  have hI : PInv rv s₀ p lr 0 (s.write .x .x16 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))) :=
    ⟨⟨by rw [g _ (by decide), h.x15], fun r hr => by rw [g _ (outer_ne hr).2.2.2.2, h.keep r hr],
      h.sp, h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h14], fun _ => by rw [g _ (by decide), h10],
      by rw [gpr_write_self]; decide, hc.congr fun _ _ _ _ _ => rfl,
      hm.congr fun p hp => g _ (maskRegs_ne p hp).2.2.2.2.1, hk,
      by rw [g _ (by decide), hl]; rfl, by rw [g _ (by decide), hr]; rfl⟩
  refine WP.loop (M := isa)
    (body := .block (round .x11 .x12 (downOf p != rv) ++ round .x12 .x11 (downOf p != rv) ++
      [.subImm .x .x16 .x16 1]))
    (c := .nonzero .x .x16) (Q := PInv rv s₀ p lr 8)
    (fun (n : Nat) (t : State) => ∃ j, n = 8 - j ∧ j < 8 ∧ PInv rv s₀ p lr j t) ?_ 8 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (pairStep_ok rv hp hp3 hj ht) fun t' h' => ?_
  have ev := eval_nonzero (r := .x16) (x := 8 - (j + 1)) (by omega_arith) h'.x16
  by_cases hz : j + 1 = 8
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega_arith, 8 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, h'⟩

theorem passTail_ok (s : State) (d : Nat) (hd : d < 4096) :
    ∃ s', runBlock isa (passTail d) s = some s' ∧
      s'.gpr .x10 = s.gpr .x10 + BitVec.ofNat 64 d ∧ s'.gpr .x11 = s.gpr .x12 ∧
      s'.gpr .x12 = s.gpr .x11 ∧ (∀ r, r ≠ .x5 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x10 (s.read .x .x10 + BitVec.ofNat _ d)
  let s₂ := s₁.write .x .x5 (s₁.gpr .x11)
  let s₃ := s₂.write .x .x11 (s₂.gpr .x12)
  let s₄ := s₃.write .x .x12 (s₃.gpr .x5)
  refine ⟨s₄, by
    rw [passTail, runBlock_cons, exec_addImm_x hd, runStep_some, runBlock_cons, exec_mov, runStep_some,
      runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_nil],
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

/-- Between passes: `passTail` for encryption, `passBack` for decryption. -/
def passMove (rv : Bool) (d : Nat) : List Instr := if rv then passBack d else passTail d

theorem passMove_ok (rv : Bool) (s : State) (d : Nat) (hd : d < 4096) :
    ∃ s', runBlock isa (passMove rv d) s = some s' ∧
      s'.gpr .x10 = (if rv then s.gpr .x10 - BitVec.ofNat 64 d else s.gpr .x10 + BitVec.ofNat 64 d) ∧
      s'.gpr .x11 = s.gpr .x12 ∧
      s'.gpr .x12 = s.gpr .x11 ∧ (∀ r, r ≠ .x5 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases rv
  · exact passTail_ok s d hd
  · let s₁ := s.write .x .x10 (s.read .x .x10 - BitVec.ofNat _ d)
    let s₂ := s₁.write .x .x5 (s₁.gpr .x11)
    let s₃ := s₂.write .x .x11 (s₂.gpr .x12)
    let s₄ := s₃.write .x .x12 (s₃.gpr .x5)
    refine ⟨s₄, by
      rw [passMove, ite_eq_left rfl, passBack, runBlock_cons, exec_subImm_x hd, runStep_some,
        runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_cons,
        exec_mov, runStep_some, runBlock_nil],
      ?_, ?_, ?_, fun r h5 h10 h11 h12 => ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [s₄, s₃, s₂, s₁, gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x12),
        gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x11), gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x5),
        gpr_write_self, State.read, BitVec.setWidth_eq, ↓reduceIte]
    · simp only [s₄, s₃, gpr_write_of_ne _ _ _ (by decide : Reg.x11 ≠ .x12), gpr_write_self,
        BitVec.setWidth_eq, s₂, gpr_write_of_ne _ _ _ (by decide : Reg.x12 ≠ .x5), s₁,
        gpr_write_of_ne _ _ _ (by decide : Reg.x12 ≠ .x10)]
    · simp only [s₄, gpr_write_self, BitVec.setWidth_eq, s₃, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x11),
        s₂, s₁, gpr_write_of_ne _ _ _ (by decide : Reg.x11 ≠ .x10)]
    · simp only [s₄, s₃, s₂, s₁, gpr_write_of_ne _ _ _ h12, gpr_write_of_ne _ _ _ h11,
        gpr_write_of_ne _ _ _ h5, gpr_write_of_ne _ _ _ h10]

/-- One pass and the exchange after it (the first two passes). -/
theorem passStep_ok (rv : Bool) {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {p : Nat} (hp2 : p < 2)
    {s : State} (h : OInv rv s₀ x p s) :
    WP isa (.seq (pass (downOf p != rv)) (.block (passMove rv (if p = 0 then 120 else 136)))) s
      (OInv rv s₀ x (p + 1)) := by
  refine WP.seq (WP.mono (pass_ok rv hp (by omega_arith) h.same h.x14 h.x10 h.consts h.masks h.keys h.l h.r) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t10, t11, t12, tk, tv, tsp, tm, trd, twr⟩ :=
    passMove_ok rv s₁ (if p = 0 then 120 else 136) (by split <;> decide)
  refine WP.of_runBlock ⟨s₂, h₂, ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tk .x15 (by decide) (by decide) (by decide) (by decide), h₁.same.x15]
  · obtain ⟨a, b, c, d, -⟩ := outer_ne hr
    rw [tk r a b c d, h₁.same.keep r hr]
  · rw [tsp, h₁.same.sp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [tk .x14 (by decide) (by decide) (by decide) (by decide), h₁.x14]
  · rw [t10, h₁.x10 (Or.inr (Or.inl hp2))]
    rcases (by omega_arith : p = 0 ∨ p = 1) with rfl | rfl <;> cases rv <;>
      simp only [slotOf, kpos, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, Bool.false_eq_true,
        Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.add_zero, Nat.zero_add, Nat.mul_zero] <;>
      (apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
       omega_arith)
  · exact h₁.consts.congr fun _ _ _ _ _ => by rw [tv]
  · exact h₁.masks.congr fun p hp => by
      obtain ⟨a, b, c, d, -⟩ := maskRegs_ne p hp
      exact tk _ a b c d
  · rw [tm]; exact h₁.keys
  · rw [t11, h₁.r, passes, swap]
  · rw [t12, h₁.l, passes, swap]

/-- The setup the blocks of one call share, but for the saves. -/
theorem prepCore_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa (.seq (.block spreadPre) (.seq (.loop (.block spreadBody) (.nonzero .x .x16))
      (.block tables))) s₀ (TInv s₀) := by
  refine WP.seq (WP.mono (spreadPre_ok s₀) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (spreadLoop_ok hp h₁) fun s₂ h₂ => ?_)
  exact tables_ok h₂

/-- The passes of the block in `x5` (as a 64-bit integer) over the schedule
at `x14` (spread at `x15`), in order or (`rv`) in reverse, into `x5`. -/
theorem crypt_ok (rv : Bool) {s₀ : State} (hp : BlockPre s₀) {s : State} (h : TInv s₀ s) :
    WP isa (.seq (.block (ipCode ++ ([.addImm .x .x10 .x15 (8 * slotOf rv 0)] : List Instr)))
      (.seq (.seq (pass rv) (.block (passMove rv 120)))
        (.seq (.seq (pass (!rv)) (.block (passMove rv 136))) (.seq (pass rv) (.block fpCode))))) s
      fun s' =>
      Same s₀ s' ∧ s'.gpr .x14 = s₀.gpr .x14 ∧ s'.gpr .x5 = tdes (schOf rv s₀) (s₀.gpr .x5) ∧
      Consts s' ∧ Masks s' ∧ Keys s₀ s'.mem 48 := by
  have d0 : (downOf 0 != rv) = rv := by cases rv <;> rfl
  have d1 : (downOf 1 != rv) = !rv := by cases rv <;> rfl
  have d2 : (downOf 2 != rv) = rv := by cases rv <;> rfl
  refine WP.seq (WP.mono (encStart_ok rv h) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (d0 ▸ passStep_ok rv hp (p := 0) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (d1 ▸ passStep_ok rv hp (p := 1) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (d2 ▸ pass_ok rv hp (p := 2) (by decide) h₅.same h₅.x14 h₅.x10 h₅.consts h₅.masks
    h₅.keys h₅.l h₅.r) fun s₆ h₆ => ?_)
  obtain ⟨s₇, h₇, x5₇, rd₇, wr₇, sp₇, k₇, m₇, v₇, mk₇⟩ := fp_ok s₆ h₆.l h₆.r
  refine WP.of_runBlock ⟨s₇, h₇, ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    h₆.consts.congr (fun w _ _ _ _ => by rw [v₇]), h₆.masks.congr mk₇, by rw [m₇]; exact h₆.keys⟩⟩
  · rw [k₇ .x15 (by simp [blockKept]), h₆.same.x15]
  · have hk : r ∈ blockKept := by
      simp only [outer, blockKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [k₇ r hk, h₆.same.keep r hr]
  · rw [sp₇, h₆.same.sp]
  · rw [rd₇, h₆.same.rd]
  · rw [wr₇, h₆.same.wr]
  · rw [m₇]; exact h₆.same.frame
  · rw [k₇ .x14 (by simp [blockKept]), h₆.x14]
  · rw [x5₇, tdes_eq]
    rfl

/-- TDEA encryption of the block in `x5` (as a 64-bit integer) with the key
schedule at `x14` (spread at `x15`), into `x5`. -/
theorem enc_ok {s₀ : State} (hp : BlockPre s₀) {s : State} (h : TInv s₀ s) :
    WP isa enc s fun s' =>
      Same s₀ s' ∧ s'.gpr .x14 = s₀.gpr .x14 ∧ s'.gpr .x5 = tdes (sch s₀) (s₀.gpr .x5) ∧
      Consts s' ∧ Masks s' ∧ Keys s₀ s'.mem 48 :=
  crypt_ok false hp h

/-- TDEA decryption of the block in `x5` (as a 64-bit integer) with the key
schedule at `x14` (spread at `x15`), into `x5`. -/
theorem dec_ok {s₀ : State} (hp : BlockPre s₀) {s : State} (h : TInv s₀ s) :
    WP isa dec s fun s' =>
      Same s₀ s' ∧ s'.gpr .x14 = s₀.gpr .x14 ∧ s'.gpr .x5 = tdesDec (sch s₀) (s₀.gpr .x5) ∧
      Consts s' ∧ Masks s' ∧ Keys s₀ s'.mem 48 := by
  refine WP.mono (crypt_ok true hp h) fun s' ⟨a, b, c, d⟩ => ⟨a, b, ?_, d⟩
  rw [c]; exact tdes_revIf _ _

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega_arith))) (by decide)

/-! ## Keeping the callee-saved registers -/

/-- The callee-saved mask registers' slots, after the spread round keys. -/
def saveSlots : List (Reg × Nat) := (List.range 9).map fun i => (savedReg i, 384 + 8 * i)

theorem save_eq : blockSave = Spill.saveCode .x15 saveSlots := by decide

theorem restore_eq : blockRestore = Spill.restoreCode .x15 saveSlots := by decide

theorem saveSlots_facts : (∀ p ∈ saveSlots, 384 ≤ p.2 ∧ p.2 + 8 ≤ 384 + 72) ∧
    (∀ p ∈ saveSlots, p.2 % 8 = 0 ∧ p.2 < 32768) ∧ Spill.Fits saveSlots ∧
    Spill.Restorable .x15 saveSlots ∧ .x15 ∉ saveSlots.map Prod.fst ∧ .x14 ∉ saveSlots.map Prod.fst ∧
    .x5 ∉ saveSlots.map Prod.fst ∧ (∀ r ∈ outer, r ∉ saveSlots.map Prod.fst) := by
  decide

/-- The callee-saved registers the block writes. -/
def savedRegs : List Reg := (List.range 9).map savedReg

theorem mem_savedRegs {r : Reg} (h : r ∈ savedRegs) : ∃ i < 9, r = savedReg i := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem mem_saveSlots {i : Nat} (hi : i < 9) : (savedReg i, 384 + 8 * i) ∈ saveSlots :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- What the block keeps: `Same`, with the saves' slots too. -/
structure SameB (s₀ s : State) : Prop where
  x15 : s.gpr .x15 = s₀.gpr .x15
  keep : ∀ r ∈ outer, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .x15, 456⟩] s₀.mem s.mem

/-- After `prep`: the setup the blocks share, with the callee-saved
registers saved. -/
structure PrepPost (s₀ s : State) : Prop where
  same : SameB s₀ s
  x5 : s.gpr .x5 = s₀.gpr .x5
  x14 : s.gpr .x14 = s₀.gpr .x14
  consts : Consts s
  masks : Masks s
  keys : Keys s₀ s.mem 48
  slots : Spill.Saved (s₀.gpr .x15) s₀.gpr saveSlots s.mem

theorem prep_ok {s₀ : State} (hp : BlockPre s₀) : WP isa prep s₀ (PrepPost s₀) := by
  obtain ⟨hl, ho, hf, -, -, -, -, -⟩ := saveSlots_facts
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  have slotIn : ∀ p ∈ saveSlots, X.Contains ((s₀.gpr .x15) + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [← hXb]; exact Offset.contains_base _ (by have := hl p hp'; omega_arith) (by have := hl p hp'; omega_arith)
  rw [prep, save_eq]
  apply WP.seq
  refine WP.mono (Spill.save_wp ho fun p hp' => ⟨X, hX, slotIn p hp'⟩) fun s₁ st => ?_
  have saveF : Frame [⟨(s₀.gpr .x15) + BitVec.ofNat 64 384, 72⟩] s₀.mem s₁.mem := by
    rw [st.mem]; exact Spill.saveMem_frame hl (by decide) _ _ _
  have bp₁ : BlockPre s₁ :=
    ⟨by rw [st.rd, st.wr, st.gpr]; exact hp.sched, by rw [st.wr, st.gpr]; exact hp.scr,
      by rw [st.gpr]; exact hp.disj⟩
  have sch₁ : sch s₁ = sch s₀ := by
    simp only [sch, st.gpr]
    exact scheduleAt_frame saveF fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact (hp.disj.sub_left (Offset.sub_base _ (by decide))).symm
  refine WP.mono (prepCore_ok bp₁) fun s₂ h₂ => ?_
  have sv : Spill.Saved (s₀.gpr .x15) s₀.gpr saveSlots s₂.mem := by
    have h := Spill.saveMem_saved hf s₀.mem (s₀.gpr .x15) s₀.gpr
    rw [← st.mem] at h
    refine h.frame_in hl h₂.same.frame fun r hr' => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    simp only [xR, st.gpr]
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
      exact ⟨_, List.mem_singleton_self _, by simp only [xR, st.gpr]; exact Region.sub_prefix (by decide)⟩
  · rw [h₂.x5, st.gpr]
  · rw [h₂.x14, st.gpr]
  · have := h₂.keys i hi
    simp only [sch₁, st.gpr] at this
    exact this

/-- The callee-saved registers restored. -/
theorem restore_ok' {s₀ s : State} (hp : BlockPre s₀) (h15 : s.gpr .x15 = s₀.gpr .x15)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hs : Spill.Saved (s₀.gpr .x15) s₀.gpr saveSlots s.mem) :
    WP isa (.block blockRestore) s (Spill.Restored s₀.gpr saveSlots s) := by
  obtain ⟨hl, ho, -, hr, -, -, -, -⟩ := saveSlots_facts
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  have slotIn : ∀ p ∈ saveSlots, X.Contains ((s₀.gpr .x15) + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [← hXb]; exact Offset.contains_base _ (by have := hl p hp'; omega_arith) (by have := hl p hp'; omega_arith)
  rw [restore_eq]
  refine Spill.restore_wp h15 ho hr (fun p hp' => ?_) hs
  rw [hrd, hwr]
  exact ⟨X, List.mem_append_right _ hX, slotIn p hp'⟩

/-- TDEA encryption of the block in `x5` (as a 64-bit integer) with the key
schedule at `x14`, into `x5`. -/
theorem block_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa block s₀ fun s =>
      SameB s₀ s ∧ s.gpr .x14 = s₀.gpr .x14 ∧ s.gpr .x5 = tdes (sch s₀) (s₀.gpr .x5) ∧
      ∀ i < 9, s.gpr (savedReg i) = s₀.gpr (savedReg i) := by
  obtain ⟨-, -, -, -, h15, h14, h5, hout⟩ := saveSlots_facts
  rw [block]
  apply WP.seq
  refine WP.mono (prep_ok hp) fun s₁ h₁ => ?_
  have bp₁ : BlockPre s₁ :=
    ⟨by rw [h₁.same.rd, h₁.same.wr, h₁.x14]; exact hp.sched,
      by rw [h₁.same.wr, h₁.same.x15]; exact hp.scr, by rw [h₁.x14, h₁.same.x15]; exact hp.disj⟩
  have sch₁ : sch s₁ = sch s₀ := by
    simp only [sch, h₁.x14]
    exact scheduleAt_frame h₁.same.frame fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hp.disj.symm
  have t₁ : TInv s₁ s₁ := ⟨Same.refl _, rfl, rfl, h₁.consts, h₁.masks, fun i hi => by
    rw [h₁.same.x15, sch₁]; exact h₁.keys i hi⟩
  apply WP.seq
  refine WP.mono (enc_ok bp₁ t₁) fun s₂ ⟨same₂, x14₂, x5₂, _, _, _⟩ => ?_
  refine WP.mono (restore_ok' hp (by rw [same₂.x15, h₁.same.x15]) (by rw [same₂.rd, h₁.same.rd])
    (by rw [same₂.wr, h₁.same.wr]) (h₁.slots.frame_in (lo := 384) (n := 72)
      (saveSlots_facts.1) same₂.frame fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        simp only [xR, h₁.same.x15]
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
    exact ⟨_, List.mem_singleton_self _, by simp only [xR, h₁.same.x15]; exact Region.sub_prefix (by decide)⟩
  · rw [h₃.other _ h14, x14₂, h₁.x14]
  · rw [h₃.other _ h5, x5₂, sch₁, h₁.x5]
  · exact h₃.gpr_of (.inl (List.mem_map.mpr ⟨_, mem_saveSlots hi, rfl⟩))

end VG.Proof.CmacTripleDes.AArch64
