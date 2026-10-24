module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.State
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.CallLay

/-! The shared emitted table supplies every exact-recognition record. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups
open VG.Proof.Ffdh.VettedTableFacts

theorem tableOfBytes (gs : List Group) (ptr : Addr) (s : State)
    (read : InRegions (s.rd ++ s.wr) ptr (gs.flatMap Group.bytes).length)
    (bytes : Spec.Rsa.bytesAt s.mem ptr (gs.flatMap Group.bytes).length = gs.flatMap Group.bytes)
    (bound : (gs.flatMap Group.bytes).length ≤ 17744)
    (valid : ∀ g ∈ gs, 0 < g.len ∧ g.len < 2 ^ 31 ∧ g.bits < 2 ^ 32) :
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

private theorem singleton_disjoint {name : String} {words : List (BitVec 64)}
    {s : State} {stack : Nat} (hc : ConstsOk [(name, words)] stack s) :
    ∀ r ∈ s.wr, (⟨s.syms name, 8 * words.length⟩ : Region).Disjoint r := by
  have member : (⟨s.syms name, 8 * words.length⟩ : Region) ∈ constRegs [(name, words)] s :=
    List.mem_cons_self
  exact (hc.2.2 _ member).2.1

theorem consts_table_after {s t : State} {stack : Nat} {B : Addr} {Z : Nat} {rs : List Reg}
    (hc : ConstsOk tableConsts stack s) (frame : Frame [⟨B, Z⟩] s.mem t.mem)
    (rest : VG.Proof.MlKem.X86_64.Keep rs s t) (workspace : (⟨B, Z⟩ : Region) ∈ s.wr) :
    TableAt (s.syms tableSym) groups t := by
  have disjoint := singleton_disjoint (name := tableSym) (words := tableWords) hc _ workspace
  have size : 8 * tableWords.length = tableBytes.length := by
    rw [tableWords_length, tableBytes_length]
  rw [size] at disjoint
  have read : InRegions (t.rd ++ t.wr) (s.syms tableSym) tableBytes.length := by
    rw [rest.2.1, rest.2.2]
    exact consts_read hc
  have bytes : Spec.Rsa.bytesAt t.mem (s.syms tableSym) tableBytes.length = tableBytes := by
    rw [VG.Proof.Rsa.rsa_bytes_frame frame (by rw [tableBytes_length]; decide)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact disjoint)]
    exact consts_bytes hc
  apply tableOfBytes groups _ t read bytes
    (by change tableBytes.length ≤ 17744; rw [tableBytes_length])
  intro g hg
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Ffdh.X86_64.VettedValidation
