import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Round
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

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
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · simp [hj]
  · simp [show ¬ 64 + j < 64 by omega]

theorem getLsbD_vdword (x : BitVec 128) {h j : Nat} (hj : j < 64) :
    (vdword x h).getLsbD j = x.getLsbD (64 * h + j) := by
  simp [vdword, hj, Nat.add_comm]

theorem getLsbD_shr2 (x : BitVec 128) (k : Nat) {h j : Nat} (hh : h < 2) (hj : j < 64) :
    (shr2 x k).getLsbD (64 * h + j) = (decide (2 * k + j < 64) && x.getLsbD (64 * h + (2 * k + j))) := by
  rw [shr2, getLsbD_ofVDwords _ _ hh hj]
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
  · simp only [BitVec.getLsbD_ushiftRight, ite_true, ite_false, show (1 : Nat) ≠ 0 by decide]
    by_cases h' : 2 * k + j < 64
    · rw [getLsbD_vdword _ h', decide_eq_true h', Bool.true_and]
    · rw [decide_eq_false h', Bool.false_and, BitVec.getLsbD_of_ge _ _ (by omega)]

theorem shr2_zero (x : BitVec 128) : shr2 x 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := getLsbD_shr2 x 0 (h := i / 64) (j := i % 64) (by omega) (by omega)
  rw [show 64 * (i / 64) + i % 64 = i by omega, show 64 * (i / 64) + (2 * 0 + i % 64) = i by omega,
    decide_eq_true (by omega), Bool.true_and] at this
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
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
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
  refine ⟨s₆, ?_, ?_, fun w h1 h2 h3 h4 => ?_, rfl⟩
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
      ⟨i / 64, i % 64, by omega, by omega, by omega⟩
    have he : 8 * h + j / 8 < 16 := by omega
    obtain ⟨g64, ghalf, gpos⟩ := gather_facts (8 * h + j / 8) he
    have hT : T.getLsbD (64 * h + j) = (vbyte (shr2 x ((gatherIndex (8 * h + j / 8)).toNat / 16))
        ((gatherIndex (8 * h + j / 8)).toNat % 16)).getLsbD (j % 8) := by
      have := getLsbD_ofVBytes (fun i =>
        let idx := (vbyte (s₃.v .v5) i).toNat
        if idx < 16 * 4 then tableByte s₃.v .v0 idx else 0) he (show j % 8 < 8 by omega)
      rw [show 8 * (8 * h + j / 8) + j % 8 = 64 * h + j by omega] at this
      rw [show T = _ from rfl, this]
      simp only
      rw [v5₃, vbyte_ofVBytes _ he, ite_eq_left (by omega), tableByte,
        repeat_v0 _ (by omega), r₃ _ (by omega)]
    have hbc : (bc 63).getLsbD (64 * h + j) = decide (j % 8 < 6) := by
      have := getLsbD_ofVBytes (fun _ => (63 : BitVec 8)) he (show j % 8 < 8 by omega)
      rw [show 8 * (8 * h + j / 8) + j % 8 = 64 * h + j by omega] at this
      rw [bc, this]
      have : ∀ t < 8, (63 : BitVec 8).getLsbD t = decide (t < 6) := by decide
      exact this _ (by omega)
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, hT, hbc, getLsbD_ofVDwords _ _ hh hj,
      getLsbD_ofVDwords _ _ hh hj]
    have hj8 : j = 8 * (j / 8) + j % 8 := by omega
    have hsp : ∀ (K : BitVec 64), (spread K).getLsbD j =
        if j % 8 < 6 then K.getLsbD (6 * (7 - boxOf (j / 8)) + j % 8) else offsets.getLsbD j := by
      intro K
      rw [hj8, getLsbD_spread K (by omega) (by omega), offsets_bits _ (by omega) _ (by omega)]
      simp only [show (8 * (j / 8) + j % 8) % 8 = j % 8 by omega,
        show (8 * (j / 8) + j % 8) / 8 = j / 8 by omega]
      by_cases h6 : j % 8 < 6
      · simp [h6]
      · simp [h6, show 6 ≤ j % 8 by omega]
    have hoff : j % 8 < 6 → offsets.getLsbD j = false := by
      intro h6
      rw [hj8, offsets_bits _ (by omega) _ (by omega), decide_eq_false (by omega), Bool.false_and]
    have hbox : (8 * h + j / 8) % 8 = j / 8 := by omega
    rw [hbox] at gpos
    -- The gathered bit.
    have hg : j % 8 < 6 → (vbyte (shr2 x ((gatherIndex (8 * h + j / 8)).toNat / 16))
        ((gatherIndex (8 * h + j / 8)).toNat % 16)).getLsbD (j % 8) =
        (vdword x h).getLsbD (6 * (7 - boxOf (j / 8)) + j % 8) := by
      intro h6
      rw [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true (by omega), Bool.true_and,
        show 8 * ((gatherIndex (8 * h + j / 8)).toNat % 16) + j % 8 =
          64 * h + (8 * ((gatherIndex (8 * h + j / 8)).toNat % 8) + j % 8) by omega,
        getLsbD_shr2 _ _ hh (by omega), decide_eq_true (by omega), Bool.true_and,
        getLsbD_vdword _ (by omega)]
      congr 1
      omega
    have hite : ∀ (a b : BitVec 64), (if h = 0 then a.getLsbD j else b.getLsbD j) =
        ([a, b].getD h 0).getLsbD j := by
      intro a b; rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl
    have hvd : ∀ h' < 2, vdword x h' = [vdword x 0, vdword x 1].getD h' 0 := by
      intro h' hh'; rcases (by omega : h' = 0 ∨ h' = 1) with rfl | rfl <;> rfl
    have hsp' : ([spread (vdword x 0), spread (vdword x 1)].getD h 0) = spread (vdword x h) := by
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl
    rw [hite, hite, hsp', show ([offsets, offsets].getD h 0) = offsets by
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl, hsp]
    by_cases h6 : j % 8 < 6
    · rw [decide_eq_true h6, Bool.and_true, hg h6, hoff h6, Bool.xor_false, ite_eq_left h6]
    · rw [decide_eq_false h6, Bool.and_false, Bool.false_xor, ite_eq_right h6]
  · simp only [s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h4, v_setV_of_ne _ _ h3,
      v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h1]

end VG.Proof.CmacTripleDes.AArch64
