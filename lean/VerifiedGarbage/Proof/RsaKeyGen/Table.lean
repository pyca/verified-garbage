import VerifiedGarbage.Proof.RsaKeyGen.Primes
import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The table of small primes

`Impl.RsaKeyGen.X86_64.Candidate.slots` is the candidates' table: the primes
3 to 3671, 3, then the primes 3673 to 8161. Its entries are odd, from 3 to
8161 (`tabEntry_facts`), and trial division by its first 512 (or all 1024)
entries is `obviouslyComposite` for primes of up to 1024 (or more) bits
(`trialAny_eq`). The primes are evaluated once, as a literal
(`primes.lit_eq`).
-/

namespace VG.Impl.RsaKeyGen

materialize_value primes

end VG.Impl.RsaKeyGen

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86_64.Candidate

theorem primes_length : primes.length = 1024 := by rw [primes.lit_eq]; decide +kernel

theorem three_mem : 3 ∈ (primes.take 512).drop 1 := by rw [primes.lit_eq]; decide +kernel

theorem slots_length : slots.length = 1024 := by
  simp only [slots, List.length_append, List.length_drop, List.length_take, primes_length, List.length_singleton]
  omega

theorem getD_of_lt {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem slots_all : slots.all (fun s => s % 2 == 1 && decide (3 ≤ s) && decide (s < 8162)) = true := by
  unfold slots; rw [primes.lit_eq]; decide +kernel

/-- The table's entries are odd, from 3 to 8161. -/
theorem tabEntry_facts {i : Nat} (hi : i < 1024) : tabEntry i % 2 = 1 ∧ 3 ≤ tabEntry i ∧ tabEntry i < 8162 := by
  have h := List.all_eq_true.mp slots_all (slots[i]'(by rw [slots_length]; exact hi)) (List.getElem_mem _)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have : tabEntry i = slots[i]'(by rw [slots_length]; exact hi) := by
    unfold tabEntry; exact getD_of_lt _
  rw [this]; exact ⟨h.1.1, h.1.2, h.2⟩

/-- Trial division by the first `4 n` entries of the table. -/
def trialAny (n c : Nat) : Bool := (List.range (4 * n)).any fun i => c % tabEntry i == 0

theorem range_map_tabEntry (n : Nat) (hn : n ≤ 1024) : (List.range n).map tabEntry = slots.take n := by
  apply List.ext_getElem (by simp [slots_length]; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, tabEntry]
  exact getD_of_lt _

theorem any_mem_congr {l₁ l₂ : List Nat} (p : Nat → Bool) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.any p = l₂.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, (h x).mp hx, hp⟩, fun ⟨x, hx, hp⟩ => ⟨x, (h x).mpr hx, hp⟩⟩

theorem smallPrimes_lt {s : Nat} (h : s ∈ smallPrimes) : s < 8162 := by
  unfold smallPrimes at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

/-- The table's trial division is `obviouslyComposite`, for a prime of
`64 w` bits. -/
theorem trialAny_eq {w c : Nat} (hc : 8161 < c) :
    trialAny (if 17 ≤ w then 256 else 128) c = obviouslyComposite (64 * w) c := by
  unfold trialAny obviouslyComposite
  have hne : ∀ l : List Nat, (∀ s ∈ l, s ∈ smallPrimes) →
      l.any (fun s => c % s == 0 && c != s) = l.any (fun s => c % s == 0) := by
    intro l hl
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨fun ⟨x, hx, h1, _⟩ => ⟨x, hx, h1⟩, fun ⟨x, hx, h1⟩ => ⟨x, hx, h1, by
      have := smallPrimes_lt (hl x hx); omega⟩⟩
  rw [hne _ fun s hs => List.mem_of_mem_take (List.mem_of_mem_drop hs), ← primes_eq]
  rw [show (fun i => c % tabEntry i == 0) = (fun s => c % s == 0) ∘ tabEntry from rfl, ← List.any_map]
  unfold trialPrimes
  by_cases hw : 17 ≤ w
  · simp only [hw, ↓reduceIte, show 1024 < 64 * w by omega]
    rw [range_map_tabEntry _ (by decide), show 4 * 256 = 1024 from rfl,
      List.take_of_length_le (Nat.le_of_eq slots_length)]
    apply any_mem_congr
    intro x
    unfold slots
    have hsplit : (primes.take 1024).drop 1 = (primes.take 512).drop 1 ++ primes.drop 512 := by
      rw [List.take_of_length_le (Nat.le_of_eq primes_length), ← List.drop_append_of_le_length (by
        simp [primes_length]), List.take_append_drop]
    rw [hsplit]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ((h | rfl) | h)
      · exact .inl h
      · exact .inl three_mem
      · exact .inr h
    · rintro (h | h)
      · exact .inl (.inl h)
      · exact .inr h
  · simp only [hw, ↓reduceIte, show ¬ 1024 < 64 * w by omega]
    rw [range_map_tabEntry _ (by decide), show 4 * 128 = 512 from rfl]
    apply any_mem_congr
    intro x
    unfold slots
    have hl : ((primes.take 512).drop 1 ++ [3]).length = 512 := by
      simp only [List.length_append, List.length_drop, List.length_take, primes_length, List.length_singleton]
      omega
    simp only [List.take_append_of_le_length (Nat.le_of_eq hl.symm), List.take_of_length_le (Nat.le_of_eq hl),
      List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl)
      · exact h
      · exact three_mem
    · exact .inl

end VG.Proof.RsaKeyGen
