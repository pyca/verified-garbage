module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Byte strings in memory, for the RSA padding functions

What the proofs of the padding functions on every target use of
`Spec.Rsa.bytesAt`: it keeps its bytes while memory changes elsewhere
(`bytesAt_frame`), and it is the list of its bytes (`bytesAt_eq`,
`bytesAt_getD`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig

open VG

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem wordsAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n * 8⟩ r) (hn : n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (r := ⟨p, n * 8⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

theorem bytesAt_len (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- A string of bytes from each of its bytes. -/
theorem bytesAt_eq {m : Mem} {p : Addr} {xs : List Byte}
    (h : ∀ i < xs.length, m (p + BitVec.ofNat 64 i) = xs.getD i 0) :
    Spec.Rsa.bytesAt m p xs.length = xs := by
  apply List.ext_getElem (bytesAt_len _ _ _)
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  rw [h i h₂, ← List.getElem_eq_getD 0]

/-- Byte `i` of a string of bytes. -/
theorem bytesAt_getD {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  rw [← List.getElem_eq_getD (h := by rw [bytesAt_len]; exact hi) d]
  simp [Spec.Rsa.bytesAt]

theorem getD_append_right {α : Type} (l l' : List α) (d : α) {n : Nat} (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_append_left {α : Type} (l l' : List α) (d : α) {n : Nat} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

end VG.Proof.RsaPkcs1Sig
