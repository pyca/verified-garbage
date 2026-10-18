module

public import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.IntervalCases

/-! Byte-level characterization shared by native subgroup candidate shapers. -/
@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Bignum VG.Proof.Ffdh.ParameterCandidate

theorem topByte_seven (b : Byte) : topByte 7 b = b ||| 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [topByte]

theorem qShape_memory {m : Mem} {op : Addr} {bs : List Byte}
    (hn : 2 ≤ bs.length) (hb : bs.length < 2 ^ 64)
    (hbytes : ∀ i < bs.length, m (op + BitVec.ofNat 64 i) = bs.getD i 0) :
    Spec.Rsa.bytesAt ((m.writeW op (m op ||| (128#8))).writeW
      (op + BitVec.ofNat 64 (bs.length - 1))
      (m (op + BitVec.ofNat 64 (bs.length - 1)) ||| (1#8))) op bs.length = shapedOctets bs 7 := by
  have hne : bs ≠ [] := by intro h; simp [h] at hn
  apply List.ext_getElem
  · rw [bytesAt_length, shapedOctets, lastOne_length (by simp [topCut]), topCut_length hne]
  · intro i hi hi'
    have hil : i < bs.length := by simpa only [bytesAt_length] using hi
    have htop : (topCut bs 7).length = bs.length := topCut_length hne 7
    have hs := lastOne_getD (bs := topCut bs 7) (i := i) (by omega)
    rw [htop, topCut_getD, topByte_seven] at hs
    have h0 : m op = bs.getD 0 0 := by simpa using hbytes 0 (by omega)
    have hlast := hbytes (bs.length - 1) (by omega)
    have hget : (shapedOctets bs 7)[i] = (shapedOctets bs 7).getD i 0 := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [hget, shapedOctets, hs]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range,
      WriteBytes.writeW8_apply]
    by_cases he : i + 1 = bs.length
    · have hie : i = bs.length - 1 := by omega
      subst i
      simp [he, hlast, show bs.length - 1 ≠ 0 by omega]
    · have hne' := Offset.add_ofNat_ne op (by omega : i < 2 ^ 64)
        (by omega : bs.length - 1 < 2 ^ 64) (by omega : i ≠ bs.length - 1)
      rw [ite_eq_right hne']
      by_cases hiz : i = 0
      · subst i; simp [he, h0]
      · have hne0 : op + BitVec.ofNat 64 i ≠ op := by
          simpa using Offset.add_ofNat_ne op (by omega : i < 2 ^ 64)
            (by decide : 0 < 2 ^ 64) hiz
        simp [he, hiz, hne0, hbytes i hil]

end VG.Proof.Dsa.Generation
