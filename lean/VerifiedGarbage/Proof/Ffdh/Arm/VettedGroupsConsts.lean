module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem

/-! The generated constant quadwords contain the exact domain-table bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups

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

private theorem consts_singleton_held {name : String} {words : List (BitVec 64)}
    {stack : Nat} {s : State} (hc : ConstsOk [(name, words)] stack s) :
    ∀ j < words.length, s.mem.readW (State.addr (s.syms name) + BitVec.ofNat 64 (8 * j)) 64 = words.getD j 0 := by
  intro j hj
  exact hc.2.1 (name, words) List.mem_cons_self j hj

theorem consts_singleton_regions {name : String} {words : List (BitVec 64)}
    {stack : Nat} {s : State} (hc : ConstsOk [(name, words)] stack s) :
    (State.addr (s.syms name)).toNat + 8 * words.length ≤ 2 ^ 32 ∧
    (∀ r ∈ s.wr, (⟨State.addr (s.syms name), 8 * words.length⟩ : Region).Disjoint r) ∧
    ∀ r ∈ abi.reserved stack s, (⟨State.addr (s.syms name), 8 * words.length⟩ : Region).Disjoint r := by
  have regions := hc.2.2.1
  have same : constRegs [(name, words)] s = [(⟨State.addr (s.syms name), 8 * words.length⟩ : Region)] := rfl
  rw [same] at regions
  have result := regions (⟨State.addr (s.syms name), 8 * words.length⟩ : Region) List.mem_cons_self
  exact result

private theorem consts_singleton_read {name : String} {words : List (BitVec 64)}
    {stack : Nat} {s : State} (hc : ConstsOk [(name, words)] stack s) :
    InRegions (s.rd ++ s.wr) (State.addr (s.syms name)) (8 * words.length) := by
  have member : (⟨State.addr (s.syms name), 8 * words.length⟩ : Region) ∈ s.rd := by
    apply List.mem_of_mem_drop
    rw [hc.1]
    exact List.mem_cons_self
  exact ⟨_, List.mem_append_left _ member, Region.contains_self _ _⟩

theorem consts_singleton_symEq {name : String} {words : List (BitVec 64)} {s t : State}
    (relation : ∀ c ∈ [(name, words)], symAddr s c.1 = symAddr t c.1) :
    s.syms name = t.syms name :=
  symAddr_eq_iff.mp (relation (name, words) List.mem_cons_self)

theorem consts_table_read {stack : Nat} {s : State} (hc : ConstsOk tableConsts stack s) :
    InRegions (s.rd ++ s.wr) (State.addr (s.syms tableSym)) tableBytes.length := by
  have read := consts_singleton_read (name := tableSym) (words := tableWords) hc
  simpa only [tableWords_length, tableBytes_length] using read

theorem consts_table_bytes {stack : Nat} {s : State} (hc : ConstsOk tableConsts stack s) :
    Spec.Rsa.bytesAt s.mem (State.addr (s.syms tableSym)) tableBytes.length = tableBytes := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro i hi hj
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    have held := consts_singleton_held (name := tableSym) (words := tableWords) hc
    rw [table_held_byte held hj]
    exact (List.getElem_eq_getD (h := hj) 0).symm

end VG.Proof.Ffdh.Arm.VettedGroups
