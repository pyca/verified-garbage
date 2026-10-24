module

import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Ffdh.VettedGroups
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Rsa

/-! The generated constant quadwords contain the exact domain-table bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.VettedTableFacts
open VG VG.Impl.Ffdh.VettedGroups

theorem groupBytes_length (g : Group) : g.bytes.length = 8 + 3 * g.len := by
  simp only [Group.bytes, wordBytes, List.length_append, List.length_map, List.length_range,
    Group.domain, VG.Proof.Rsa.i2osp_length]
  omega

theorem tableBytes_length : tableBytes.length = 17744 := by
  simp only [tableBytes, groups, List.flatMap_cons, List.flatMap_nil, List.length_append,
    groupBytes_length, List.length_nil]

theorem tableWords_length : tableWords.length = 2218 := by
  simp only [tableWords, List.length_map, List.length_range, tableBytes_length]

theorem tableWords_getD {i : Nat} (hi : i < tableWords.length) :
    tableWords.getD i 0 = tableWord i := by
  simp only [tableWords, List.length_map, List.length_range] at hi
  simp only [tableWords, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem tableWord_byte {i : Nat} (hi : i < tableBytes.length) :
    (tableWord (i / 8)).extractLsb' (8 * (i % 8)) 8 = tableBytes.getD i 0 := by
  unfold tableWord
  change ((show Mem from fun a : Addr => tableBytes.getD a.toNat 0).read  (BitVec.ofNat 64 (8 * (i / 8))) 8).extractLsb' (8 * (i % 8)) 8 = _
  rw [Mem.extractLsb'_read _ _ (by omega)]
  simp only [BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by rw [tableBytes_length] at hi; omega)]

theorem table_held_byte {m : Mem} {base : Addr}
    (held : ∀ i < tableWords.length, m.readW (base + BitVec.ofNat 64 (8 * i)) 64 = tableWords.getD i 0)
    {i : Nat} (hi : i < tableBytes.length) :
    m (base + BitVec.ofNat 64 i) = tableBytes.getD i 0 := by
  have word := held (i / 8) (by rw [tableWords_length]; rw [tableBytes_length] at hi; omega)
  rw [tableWords_getD (by rw [tableWords_length]; rw [tableBytes_length] at hi; omega)] at word
  have addr : base + BitVec.ofNat 64 i =
      (base + BitVec.ofNat 64 (8 * (i / 8))) + BitVec.ofNat 64 (i % 8) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod]
  rw [addr, ← Mem.extractLsb'_read m _ (n := 8) (by omega), ← tableWord_byte hi, ← word]
  rfl

end VG.Proof.Ffdh.VettedTableFacts
