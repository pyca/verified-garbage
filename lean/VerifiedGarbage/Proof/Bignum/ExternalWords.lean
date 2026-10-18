module

public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-! Word preservation for writes confined to an external byte buffer. -/
@[expose] public section
namespace VG.Proof.Bignum
open VG

/-- A write confined to an external byte buffer preserves workspace words. -/
theorem words_outside_bytes {B op : Addr} {Z len : Nat} {m m' : Mem}
    (hz : Z ≤ 2 ^ 64)
    (hf : ∀ a, (∀ i < len, a ≠ off op i) → m' a = m a)
    (hs : ∀ i < len, Z ≤ ofs B (off op i)) :
    ∀ d, d + 8 ≤ Z → word m' B d = word m B d := by
  intro d hd
  apply Mem.readW_congr
  intro i hi
  have ha : off B d + BitVec.ofNat 64 i = off B (d + i) := by
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  apply hf
  intro j hj he
  have hs' := hs j hj
  rw [← he] at hs'
  have heq := ofs_off B (d := d + i) (i := 0) (by omega)
  simp only [BitVec.add_zero, Nat.add_zero] at heq
  rw [heq] at hs'
  omega

end VG.Proof.Bignum
