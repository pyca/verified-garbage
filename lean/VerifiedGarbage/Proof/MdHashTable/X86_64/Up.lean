module

public import VerifiedGarbage.Proof.HmacTable.X86_64.Up
public import VerifiedGarbage.Proof.HashTable.X86_64

/-!
# Tables of the interface `MdHash` on x86-64: what a caller's cleanup needs

A function that calls a hash function's through a table of `MdHash` clears the
stack they use and the registers they write: what its cleanup needs of each
variant's functions (`MdUp`, `HmacTable/X86_64/Up.lean`), as `TFill`'s rules
for the indirect calls of the code with stubs in their place (`stubFns`) need
it.
-/

@[expose] public section

namespace VG.Proof.MdHashTable.X86_64

open VG.X86_64.Scrub
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
export VG.Proof.HmacTable.X86_64 (MdUp variants_mdUp)

/-- What the cleanup needs of each of the functions PSS calls through a table
of `vs`. -/
theorem mdFns_up {vs : List MdHash} (hv : ∀ w ∈ vs, MdUp w) :
    (∀ q ∈ (fnsOf vs).init, upCallee q.2 8 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).comp, upCallee q.2 8 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).dig, upCallee q.2 8 = true ∧ q.1 ∈ names vs) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq <;>
    obtain ⟨n1, n2, n3, n4, n5⟩ := mem_names hw
  · exact ⟨(hv w hw).init, n1⟩
  · exact ⟨(hv w hw).comp, n4⟩
  · exact ⟨(hv w hw).dig, n5⟩

end VG.Proof.MdHashTable.X86_64

namespace VG.Proof.HashTable.X86_64

open VG.X86_64.Scrub
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.MdHashTable.X86_64 (MdUp tables)

/-- A stub in the place of each of the streaming functions. -/
def stubFns : Impl.Mgf1.X86_64.Table.Fns :=
  ⟨[("t", tableStub 8)], [("t", tableStub 8)], [("t", tableStub 8)]⟩

/-- What the cleanup needs of each of the streaming functions the tables of
`vs` hold. -/
theorem fns_up {vs : List MdHash} (hv : ∀ w ∈ vs, MdUp w) :
    (∀ q ∈ (fnsOf vs).init, upCallee q.2 8 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).upd, upCallee q.2 8 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).fin, upCallee q.2 8 = true ∧ q.1 ∈ names vs) := by
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
  simp only [names, MdHashTable.X86_64.names, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hf⟩ := h
  exact .inl ⟨t, ht, hf⟩

end VG.Proof.HashTable.X86_64
