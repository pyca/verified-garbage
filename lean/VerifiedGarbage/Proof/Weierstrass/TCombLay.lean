import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb

/-!
# The fixed-base comb from tables in memory: where it keeps its numbers

As the comb's (`CombLay`), with the table of bits `w J` bytes, past the
scalar's `kbytes` cleared in words by the comb (`TCombLay`). `TCombCfg.toComb` is the comb of
the same slots with no tables, whose layout this one gives
(`TCombLay.comb`): so the addition's facts are the comb's.
-/

namespace VG.Proof.Weierstrass

open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont

/-- The comb of the same slots, with `J` empty tables. -/
def _root_.VG.Impl.Weierstrass.AArch64.TCombCfg.toComb (K : TCombCfg) : CombCfg where
  M := K.M
  S := K.S
  A := K.A
  E := K.E
  D := K.D
  neg := K.neg
  zero := K.zero
  bits := K.bits
  tbl := List.replicate K.J []
  start := K.start
  one := K.one

theorem _root_.VG.Impl.Weierstrass.AArch64.TCombCfg.toComb_J (K : TCombCfg) : K.toComb.J = K.J := by
  simp [CombCfg.J, TCombCfg.toComb]

/-- The words of the table of bits that the comb clears, past the scalar's
`kbytes`, up to `w J`. -/
def _root_.VG.Impl.Weierstrass.AArch64.TCombCfg.zw (K : TCombCfg) : Nat := (K.w * K.J - K.kbytes + 7) / 8

/-- What the comb writes: the comb's, and the cleared words of the table of
bits. -/
def tcombW (K : TCombCfg) : List (Nat × Nat) := combW K.toComb ++ [(K.bits + K.kbytes, 8 * K.zw)]

/-- The comb's layout (`CombLay` of `toComb`), the table of bits of `w J` bytes (and its cleared words) in the working space,
apart from what the loop writes and its cleared words apart from the
slots and the modulus, with offsets `ldrb` encodes, and the digits'
width and number in range. -/
structure TCombLay (K : TCombCfg) (size : Nat) : Prop where
  comb : CombLay K.toComb size
  w : 4 ≤ K.w ∧ K.w < 9
  kbytes : K.kbytes ≤ K.w * K.J
  bits : K.bits + K.kbytes + 8 * K.zw ≤ size
  bits8 : (K.bits + K.kbytes) % 8 = 0
  bitsw : K.bits + K.w * K.J ≤ 4096
  bits_w : ∀ w ∈ combW K.toComb, K.bits + K.kbytes + 8 * K.zw ≤ w.1 ∨ w.1 + w.2 ≤ K.bits
  bits_sl : ∀ x ∈ K.M.mo :: combSlots K.toComb,
    K.bits + K.kbytes + 8 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes
  n8 : K.M.n ≤ 9
  n2 : K.M.n % 2 = 1 → K.M.n = 9 ∧ K.E.y = K.E.x + 8 * K.M.n
  e16 : K.E.x % 16 = 0 ∧ (K.M.n % 2 = 0 → K.E.y % 16 = 0)
  tbl : 16 * K.M.n * K.H ≤ 32768 ∧ K.tblBytes < 65536

end VG.Proof.Weierstrass
