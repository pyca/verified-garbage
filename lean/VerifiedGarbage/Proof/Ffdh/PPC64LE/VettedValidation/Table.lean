module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.State
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.CallLay

/-! The shared emitted table supplies every exact-recognition record. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Impl.Ffdh.VettedGroups
open VG.Proof.Ffdh.VettedTableFacts

theorem tableOfBytes (gs : List Group) (ptr : Addr) (s : State)
    (read : InRegions (s.rd ++ s.wr) ptr (gs.flatMap Group.bytes).length)
    (bytes : Spec.Rsa.bytesAt s.mem ptr (gs.flatMap Group.bytes).length = gs.flatMap Group.bytes)
    (bound : (gs.flatMap Group.bytes).length ≤ 17744)
    (valid : ∀ g ∈ gs, 0 < g.len ∧ g.len < 2 ^ 15 ∧ g.bits < 2 ^ 15) :
    TableAt ptr gs s := by
  induction gs generalizing ptr with
  | nil => trivial
  | cons g gs ih =>
    have length := groupBytes_length g
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, length]
    have domainLength : g.domain.length = 3 * g.len := by
      simp only [Group.domain, List.length_append, VG.Proof.Rsa.i2osp_length]
      omega
    have headerLength : (wordBytes g.len ++ wordBytes g.bits).length = 8 := by
      simp only [wordBytes, List.length_append, List.length_map, List.length_range]
    have domain : (((g :: gs).flatMap Group.bytes).drop 8).take (3 * g.len) = g.domain := by
      rw [List.flatMap_cons, Group.bytes, List.append_assoc, ← headerLength,
        List.drop_left, List.take_left' domainLength]
    have tailBytes : (((g :: gs).flatMap Group.bytes).drop (8 + 3 * g.len)).take
        (gs.flatMap Group.bytes).length = gs.flatMap Group.bytes := by
      rw [List.flatMap_cons, ← length, List.drop_left, List.take_length]
    have part (d n : Nat) (size : d + n ≤ ((g :: gs).flatMap Group.bytes).length) :
        InRegions (s.rd ++ s.wr) (ptr + BitVec.ofNat 64 d) n :=
      CallLay.inRegions_sub read size (by omega)
    have slice (d n : Nat) (size : d + n ≤ ((g :: gs).flatMap Group.bytes).length) :
        Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 d) n =
          (((g :: gs).flatMap Group.bytes).drop d).take n := by
      rw [← VG.Proof.Dsa.bytesAt_slice s.mem ptr size, bytes]
    have v := valid g (by simp)
    refine ⟨⟨v.1, v.2.1, v.2.2, part 8 (3 * g.len) (by rw [total]; omega),
      (slice 8 (3 * g.len) (by rw [total]; omega)).trans domain⟩, ?_⟩
    exact ih _ (part _ _ (by rw [total]))
      ((slice _ _ (by rw [total])).trans tailBytes)
      (by rw [total] at bound; omega) (fun g hg => valid g (by simp [hg]))

private theorem singleton_held {name : String} {words : List (BitVec 64)}
    {s : State} {stack : Nat} (hc : ConstsOk [(name, words)] stack s) :
    ∀ i < words.length, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0 := by
  intro i hi
  exact hc.2.1 (name, words) List.mem_cons_self i hi

private theorem singleton_read {name : String} {words : List (BitVec 64)}
    {s : State} {stack : Nat} (hc : ConstsOk [(name, words)] stack s) :
    InRegions (s.rd ++ s.wr) (s.syms name) (8 * words.length) := by
  have member : (⟨s.syms name, 8 * words.length⟩ : Region) ∈ s.rd := by
    apply List.mem_of_mem_drop
    rw [hc.1]
    exact List.mem_cons_self
  exact ⟨_, List.mem_append_left _ member, Region.contains_self _ _⟩

theorem consts_bytes {s : State} {stack : Nat} (hc : ConstsOk tableConsts stack s) :
    Spec.Rsa.bytesAt s.mem (s.syms tableSym) tableBytes.length = tableBytes := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro i hi hj
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    have held := singleton_held (name := tableSym) (words := tableWords) hc
    rw [table_held_byte held hj]
    exact (List.getElem_eq_getD (h := hj) 0).symm

theorem consts_read {s : State} {stack : Nat} (hc : ConstsOk tableConsts stack s) :
    InRegions (s.rd ++ s.wr) (s.syms tableSym) tableBytes.length := by
  have read := singleton_read (name := tableSym) (words := tableWords) hc
  simpa only [tableWords_length, tableBytes_length] using read

theorem consts_table {s : State} {stack : Nat} (hc : ConstsOk tableConsts stack s) :
    TableAt (s.syms tableSym) groups s := by
  apply tableOfBytes groups _ s (consts_read hc) (consts_bytes hc)
    (by change tableBytes.length ≤ 17744; rw [tableBytes_length])
  intro g hg
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Ffdh.PPC64LE.VettedValidation
