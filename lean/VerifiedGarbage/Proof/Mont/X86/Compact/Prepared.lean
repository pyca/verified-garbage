module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
public import VerifiedGarbage.Proof.Mont.X86.Compact.Bounds
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
public import VerifiedGarbage.Proof.Rsa.MontContract

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

theorem layout_metadata {m : Mem} {W : Addr} {wsLen : Nat} {A : Nat → BitVec 32}
    (layout : Layout m W wsLen) (left : (A 3).toNat < 8) (right : (A 4).toNat < 8) :
    Metadata m W A (2 * wOf m W) (arrAt (wOf m W) 2) (arrAt (wOf m W) 0)
      (arrAt (wOf m W) (A 3).toNat) (arrAt (wOf m W) (A 4).toNat) := by
  obtain ⟨_, widthBound, _, ptrs⟩ := layout
  have width : w32 m W 48 = wOf m W := by
    rw [show 48 = 8 * wWord from rfl, header_low]
    change (wOf m W) % 2 ^ 32 = wOf m W
    exact Nat.mod_eq_of_lt (by omega)
  have ptr (j : Nat) (hj : j < 8) :
      w32 m W (64 + 8 * j) = (W.toNat + arrAt (wOf m W) j) % 2 ^ 32 := by
    rw [show 64 + 8 * j = 8 * arrWord j by unfold arrWord; omega, header_low, ptrs j hj,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  exact ⟨by rw [width]; omega, left, right, ptr 2 (by decide), ptr 0 (by decide), ptr _ left, ptr _ right⟩

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

theorem layout_bounds {w L a b : Nat} (fit : arrAt w 8 ≤ L)
    (left : Operand a) (right : Operand b) :
    Lay L (2 * w) (arrAt w 2) (arrAt w 0) (arrAt w a) (arrAt w b) := by
  have product := product_fits w
  have scratch := array_fit fit (j := 4) (by decide)
  have modulus := array_fit fit (j := 0) (by decide)
  have aFit := array_fit fit left.1
  have bFit := array_fit fit right.1
  have apartM := operand_apart (w := w) (j := 0) (by exact ⟨by decide, by decide, by decide⟩)
  have apartA := operand_apart (w := w) left
  have apartB := operand_apart (w := w) right
  have acc : VG.Impl.Mont.X86.Compact.accOff = 24 := rfl
  constructor
  · unfold arrAt hdrBytes; omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

end VG.Proof.Mont.X86.Compact
