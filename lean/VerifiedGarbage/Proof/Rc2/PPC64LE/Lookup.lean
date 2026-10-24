module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Scan
public import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# RC2 on PPC64LE: the lookups

`keyLookup_run`: the schedule's scan leaves key word `idx` in `r11`, for
`q = 2 idx` in `r10`. `entry_byte`: a byte table's scan leaves its byte.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem rotSum_word (q : BitVec 64) (hq : q.toNat % 2 = 0) : rotSum q [1, 2] = 8 * (q.toNat % 8) := by
  simp only [rotSum, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  split_ifs <;> omega

theorem rotSum_byte (q : BitVec 64) : rotSum q [0, 1, 2] = 8 * (q.toNat % 8) := by
  simp only [rotSum, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  split_ifs <;> omega

theorem rot_word16 (x : BitVec 64) {l : Nat} (hl : l ≤ 6) :
    (x.rotateRight (8 * l)).setWidth 16 =
      (x.extractLsb' (8 * l) 8).zeroExtend 16 ||| (x.extractLsb' (8 * (l + 1)) 8).zeroExtend 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight_of_lt (show 8 * l < 64 by omega),
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.truncate_eq_setWidth, BitVec.getLsbD_extractLsb', hj,
    decide_true, Bool.true_and]
  by_cases h8 : j < 8
  · simp [h8, show j < 64 - 8 * l by omega, show 8 * l + j < 64 by omega]
  · simp [h8, show j < 64 - 8 * l by omega, show j - 8 < 8 by omega, show j - 8 < 16 by omega]
    congr 1; omega

theorem rot_byte (x : BitVec 64) {l : Nat} (hl : l < 8) :
    (x.rotateRight (8 * l)).setWidth 8 = x.extractLsb' (8 * l) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight_of_lt (show 8 * l < 64 by omega),
    BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  simp [show j < 64 - 8 * l by omega, show 8 * l + j < 64 by omega]

/-- Key word `idx` of the schedule at `T`, from its doubleword. -/
theorem entry_word (m : Mem) (T : Addr) {idx : Nat} (hidx : idx < 64) :
    ((m.readW (T + BitVec.ofNat 64 (8 * ((BitVec.ofNat 64 (2 * idx)).toNat / 8))) 64).rotateRight
      (8 * ((BitVec.ofNat 64 (2 * idx)).toNat % 8))).setWidth 16 = (Spec.Rc2.scheduleAt m T).getD idx 0 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 * idx < 2 ^ 64 by omega),
    show 2 * idx % 8 = 2 * (idx % 4) by omega, rot_word16 _ (by omega), Proof.Rc2.read64_byte _ _ _ (by omega),
    Proof.Rc2.read64_byte _ _ _ (by omega), Offset.add_add, Offset.add_add, Spec.Rc2.scheduleAt,
    Proof.Rc2.getD_ofFn _ _ hidx]
  simp only
  rw [show 8 * (2 * idx / 8) + 2 * (idx % 4) = 2 * idx by omega,
    show 8 * (2 * idx / 8) + (2 * (idx % 4) + 1) = 2 * idx + 1 by omega]

/-- The byte at offset `q` of the table at `T`, from its doubleword. -/
theorem entry_byte (m : Mem) (T : Addr) (q : BitVec 64) :
    ((m.readW (T + BitVec.ofNat 64 (8 * (q.toNat / 8))) 64).rotateRight (8 * (q.toNat % 8))).setWidth 8 =
      m (T + q) := by
  rw [rot_byte _ (Nat.mod_lt _ (by decide)), Proof.Rc2.read64_byte _ _ _ (Nat.mod_lt _ (by decide)),
    Offset.add_add, show 8 * (q.toNat / 8) + q.toNat % 8 = q.toNat by omega, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem keyRegs : ScanRegs .r3 .r5 := ⟨by decide, by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide⟩

/-- The scan of the schedule at `r3`. -/
theorem keyLookup_run (s : State) {T : Addr} (hT : s.gpr .r3 = T) {idx : Nat} (hidx : idx < 64)
    (hq : s.gpr .r10 = BitVec.ofNat 64 (2 * idx))
    (hr : ∀ k < 16, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa keyLookup s fun t =>
      t.gpr .r11 = ((Spec.Rc2.scheduleAt s.mem T).getD idx 0).setWidth 64 ∧
      Keep [.r0, .r11, .r12, .r5] s t ∧ t.mem = s.mem := by
  have h2 : (BitVec.ofNat 64 (2 * idx)).toNat = 2 * idx := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (scan_run keyRegs s hT (rows := 16) (by decide) (lanes := [1, 2]) (by decide) (by decide)
    (bits := 16) (by decide) (by rw [hq, h2]; omega) (by rw [hq]; exact rotSum_word _ (by rw [h2]; omega)) hr)
    fun t ⟨t11, tk, tm⟩ => ⟨?_, tk, tm⟩
  rw [t11, hq, entry_word _ _ hidx]

end VG.Proof.Rc2.PPC64LE
