module
public import VerifiedGarbage.Spec.Blowfish

import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# A lookup that scans an S-box's planes a doubleword at a time

What 64-bit implementations hold while scanning S-box `j` for the index `x`
a row of eight entries (a doubleword of each plane) at a time, with one
accumulator per plane: the OR of the rows' doublewords, each masked to all
ones if the row holds `x` and to zero otherwise (`scanPlane`), which after
the last row is plane `b`'s doubleword of the row holding `x`; and that
doubleword's byte in `x`'s lane `x mod 8` is byte `b` of the entry
(`planeWord64_byte`).
-/

@[expose] public section

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- Plane `b`'s doubleword of row `k` of S-box `j`, in the schedule at `p`. -/
def planeWord64 (m : Mem) (p : Addr) (j b k : Nat) : BitVec 64 :=
  m.readW (p + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * k)) 64

/-- Plane `b`'s accumulator once rows `0, …, k - 1` are scanned for `x`. -/
def scanPlane (m : Mem) (p : Addr) (j b x k : Nat) : BitVec 64 :=
  if x / 8 < k then planeWord64 m p j b (x / 8) else 0

/-- The mask of row `k` for `x`. -/
def rowSel (x k : Nat) : BitVec 64 := if x / 8 = k then BitVec.allOnes 64 else 0

/-- Row 0, masked: the accumulator after it. -/
theorem scanPlane_one (m : Mem) (p : Addr) (j b x : Nat) :
    planeWord64 m p j b 0 &&& rowSel x 0 = scanPlane m p j b x 1 := by
  unfold scanPlane rowSel
  by_cases h : x / 8 = 0
  · rw [ite_eq_left h, ite_eq_left (by omega_arith), BitVec.and_allOnes, h]
  · rw [ite_eq_right h, ite_eq_right (by omega_arith)]
    exact BitVec.and_zero

/-- Row `k`, masked, ORed into the accumulator. -/
theorem scanPlane_succ (m : Mem) (p : Addr) (j b x k : Nat) :
    scanPlane m p j b x k ||| (planeWord64 m p j b k &&& rowSel x k) = scanPlane m p j b x (k + 1) := by
  unfold scanPlane rowSel
  by_cases h : x / 8 = k
  · subst h
    rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _),
      BitVec.and_allOnes]
    exact BitVec.zero_or
  · rw [ite_eq_right h, show planeWord64 m p j b k &&& 0 = 0 from BitVec.and_zero,
      show ∀ y : BitVec 64, y ||| 0 = y from fun _ => BitVec.or_zero]
    by_cases h' : x / 8 < k
    · rw [ite_eq_left h', ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h', ite_eq_right (by omega_arith)]

theorem scanPlane_all (m : Mem) (p : Addr) (j b : Nat) (x : Byte) :
    scanPlane m p j b x.toNat 32 = planeWord64 m p j b (x.toNat / 8) := by
  have := x.isLt
  rw [scanPlane, ite_eq_left (by omega_arith)]

/-- Byte `x mod 8` of plane `c`'s doubleword of the row holding `x` is byte
`c` of S-box `j`'s entry `x`. -/
theorem planeWord64_byte (m : Mem) (p : Addr) {j c : Nat} (hj : j < 4) (hc : c < 4) (x : Byte) :
    (planeWord64 m p j c (x.toNat / 8)).extractLsb' (8 * (x.toNat % 8)) 8 =
      (sEntry (scheduleAt m p) j x).extractLsb' (8 * c) 8 := by
  rw [sEntry_byte m p hj hc, planeWord64]
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]
  rw [Mem.extractLsb'_read m _ (Nat.mod_lt _ (by decide)), Offset.add_add]
  congr 3
  omega_arith

end VG.Proof.Blowfish
