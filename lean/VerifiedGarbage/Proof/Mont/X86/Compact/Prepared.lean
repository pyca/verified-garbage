module

import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import Init.Prelude

/-! # The reviewed prepared workspace supplies native-word metadata -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont
open VG.Proof.Rsa.Mont

theorem header_low (m : Mem) (W : Addr) (i : Nat) :
    w32 m W (8 * i) = (wordAt m W i).toNat % 2 ^ 32 := by
  unfold w32 wordAt off
  rw [← VG.Proof.Rc2.Word32.readW64_lo, BitVec.extractLsb'_toNat]
  simp only [Nat.shiftRight_zero]

theorem array_mono (w : Nat) {i j : Nat} (bound : i < j) :
    arrAt w i + 8 * (w + 2) ≤ arrAt w j := by
  have h := Nat.mul_le_mul_right (8 * (w + 2)) bound
  unfold arrAt hdrBytes
  rw [Nat.succ_mul] at h
  omega

theorem array_fit {w L j : Nat} (fit : arrAt w 8 ≤ L) (index : j < 8) :
    arrAt w j + 8 * w ≤ L := by
  have := array_mono w index
  omega

end VG.Proof.Mont.X86.Compact
