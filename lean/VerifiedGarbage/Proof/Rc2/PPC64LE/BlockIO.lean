module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Mix
public import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.PPC64LE.Rounds

/-! # RC2 on PPC64LE: loading and storing the block -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem lane (x : BitVec 64) {i : Nat} (hi : i < 4) :
    (x <<< (48 - 16 * i)) >>> 48 = ((x >>> (16 * i)).setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < 16
  · simp only [h, hj, decide_true, Bool.true_and, show 48 + j < 64 by omega, show ¬48 + j < 48 - 16 * i by omega,
      decide_false, Bool.not_false]
    rw [show 48 + j - (48 - 16 * i) = 16 * i + j by omega]
  · simp only [h, show ¬48 + j < 64 by omega, decide_false, Bool.false_and, Bool.and_false]

theorem lane3 (x : BitVec 64) : x >>> 48 = ((x >>> (16 * 3)).setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  by_cases h : j < 16
  · simp [h, hj]
  · simp only [h, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge x (48 + j) (by omega)]
    simp

theorem blockLoad_run (u : State) (hr : InRegions (u.rd ++ u.wr) (u.gpr .r4) 8) :
    WP isa (.block blockLoad) u fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .r4))) t ∧ t.mem = u.mem ∧
        Keep [.r6, .r7, .r8, .r9, .r11] u t := by
  refine WP.mono (WP.keep [.r6, .r7, .r8, .r9, .r11] (c := .block blockLoad) (Q := fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .r4))) t ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, blockLoad, dstOf]) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold blockLoad
  rrun [hr]
  intro i hi
  rw [decode_read64 _ _ _ hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact lane _ (i := 0) (by decide)
  · exact lane _ (i := 1) (by decide)
  · exact lane _ (i := 2) (by decide)
  · exact lane3 _

theorem pack_or (v : Spec.Rc2.State) :
    (v.getD 1 0).setWidth 64 <<< 16 ||| (v.getD 0 0).setWidth 64 ||| (v.getD 2 0).setWidth 64 <<< 32 |||
      (v.getD 3 0).setWidth 64 <<< 48 = pack v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pack, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h₁ : j < 16
  · simp (disch := omega) [h₁, hj, show j < 32 by omega, show j < 48 by omega]
  · by_cases h₂ : j < 32
    · simp (disch := omega) [h₁, h₂, hj, show j < 48 by omega, show j - 16 < 64 by omega, show j - 16 < 16 by omega,
        BitVec.getLsbD_of_ge]
    · by_cases h₃ : j < 48
      · simp (disch := omega) [h₁, h₂, h₃, hj, show j - 32 < 64 by omega, show ¬j - 16 < 16 by omega,
          show j - 16 - 16 = j - 32 by omega, show j - 32 < 16 by omega, BitVec.getLsbD_of_ge]
      · simp (disch := omega) [h₁, h₂, h₃, hj, show j - 48 < 64 by omega, show ¬j - 16 < 16 by omega,
          show j - 16 - 16 = j - 32 by omega, show ¬j - 32 < 16 by omega, show j - 32 - 16 = j - 48 by omega,
          BitVec.getLsbD_of_ge]

theorem blockStore_run (u : State) {v : Spec.Rc2.State} (H : Holds v u) (hw : InRegions u.wr (u.gpr .r4) 8) :
    WP isa (.block blockStore) u fun t =>
      t.mem = u.mem.writeW (u.gpr .r4) (pack v) ∧ Keep [.r11, .r12] u t := by
  refine WP.mono (WP.keep [.r11, .r12] (c := .block blockStore) (Q := fun t =>
      t.mem = u.mem.writeW (u.gpr .r4) (pack v)) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, blockStore, dstOf]) rfl) fun t ⟨a, c⟩ => ⟨a, c⟩
  have h0 := H 0 (by decide)
  have h1 := H 1 (by decide)
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  rw [wordReg_0] at h0
  rw [wordReg_1] at h1
  rw [wordReg_2] at h2
  rw [wordReg_3] at h3
  unfold blockStore
  rrun [hw, h0, h1, h2, h3]
  exact congrArg _ (pack_or v)

end VG.Proof.Rc2.PPC64LE
