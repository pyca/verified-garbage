module

public import VerifiedGarbage.Proof.HmacTable.AArch64.Up
public import VerifiedGarbage.Proof.HashTable.AArch64

/-!
# Tables of the interface `MdHash` on AArch64: what a caller's cleanup needs

A function that calls a hash function's through a table of `MdHash` clears the
stack they use and the registers they write: what its cleanup needs of each
variant's functions (`MdUp`, `HmacTable/AArch64/Up.lean`), as `TFill`'s rules
for the indirect calls of the code with stubs in their place (`stubFns`) need
it.
-/

@[expose] public section

namespace VG.Proof.MdHashTable.AArch64

open VG.AArch64 VG.AArch64.Scrub
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
export VG.Proof.HmacTable.AArch64 (MdUp variants_mdUp)

/-- What the cleanup needs of each of the functions PSS calls through a table
of `vs`. -/
theorem mdFns_up {vs : List MdHash} (hv : ∀ w ∈ vs, MdUp w) :
    (∀ q ∈ (fnsOf vs).init, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).comp, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).dig, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq <;>
    obtain ⟨n1, n2, n3, n4, n5⟩ := mem_names hw
  · exact ⟨(hv w hw).init, n1⟩
  · exact ⟨(hv w hw).comp, n4⟩
  · exact ⟨(hv w hw).dig, n5⟩

end VG.Proof.MdHashTable.AArch64

namespace VG.Proof.HashTable.AArch64

open VG.AArch64 VG.AArch64.Scrub
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (MdUp tables)

/-- A stub in the place of each of the streaming functions. -/
def stubFns : Impl.RsaOaep.AArch64.Mgf1.Table.Fns :=
  ⟨[("t", tableStub 1)], [("t", tableStub 1)], [("t", tableStub 1)]⟩

/-- What the cleanup needs of each of the streaming functions the tables of
`vs` hold. -/
theorem fns_up {vs : List MdHash} (hv : ∀ w ∈ vs, MdUp w) :
    (∀ q ∈ (fnsOf vs).init, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).upd, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).fin, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq <;>
    obtain ⟨n1, n2, n3⟩ := mem_names hw
  · exact ⟨(hv w hw).init, n1⟩
  · exact ⟨(hv w hw).upd, n2⟩
  · exact ⟨(hv w hw).fin, n3⟩

/-- The functions of the tables of `vs` are those of a function that takes
two of them. -/
theorem mem_tableFns {vs : List MdHash} {f : String} (h : f ∈ names vs) :
    f ∈ tableFns [("hash", tables vs), ("mgf1", tables vs)] := by
  simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_flatMap]
  simp only [names, MdHashTable.AArch64.names, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hf⟩ := h
  exact .inl ⟨t, ht, hf⟩

end VG.Proof.HashTable.AArch64
