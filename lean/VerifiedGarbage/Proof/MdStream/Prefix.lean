import VerifiedGarbage.Proof.MdStream.Spec

/-!
# Streaming Merkle–Damgård hash functions: prefixes of the digest

A truncated digest (SHA-224's, SHA-384's, …) is the first words of the final
hash value, each written as the same number of bytes: these facts take the
first of them, and the regions holding them.
-/

namespace VG.Proof.MdStream

/-- A region holding `n` bytes at `a` holds the first `m` of them. -/
theorem inRegions_prefix {rs : List Region} {a : Addr} {n m : Nat} (h : InRegions rs a n) (hm : m ≤ n) :
    InRegions rs a m := by
  obtain ⟨R, hR, hc⟩ := h
  exact ⟨R, hR, by unfold Region.Contains at *; omega⟩

theorem length_flatMap_range {α : Type} (f : Nat → List α) {w : Nat} (hf : ∀ k, (f k).length = w) (n : Nat) :
    ((List.range n).flatMap f).length = w * n := by
  rw [List.length_flatMap, List.map_congr_left (fun x _ => hf x), List.map_const', List.sum_replicate_nat,
    List.length_range, Nat.mul_comm]

/-- The first `w · n` elements of the lists `f k`, each of `w` elements, for
`k < m`, are those for `k < n`. -/
theorem take_flatMap_range {α : Type} (f : Nat → List α) {w : Nat} (hf : ∀ k, (f k).length = w) {n m : Nat}
    (h : n ≤ m) : ((List.range m).flatMap f).take (w * n) = (List.range n).flatMap f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.flatMap_append, List.take_append_of_le_length (by rw [length_flatMap_range f hf]),
    List.take_of_length_le (by rw [length_flatMap_range f hf])]

end VG.Proof.MdStream
