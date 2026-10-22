module

public import VerifiedGarbage.Impl.RsaKeyGen.Primes32
public import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! The shared small-prime table packed into 32-bit words. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen

theorem tabWord32_lo {j : Nat} (hj : j < 512) : tabWord32 j % 2 ^ 16 = tabEntry (2 * j) := by
  have := (tabEntry_facts (i := 2 * j) (by omega)).2.2
  unfold tabWord32; omega

theorem tabWord32_hi {j : Nat} (hj : j < 512) : tabWord32 j / 2 ^ 16 = tabEntry (2 * j + 1) := by
  have := (tabEntry_facts (i := 2 * j) (by omega)).2.2
  unfold tabWord32; omega

theorem tabWord32_lt {j : Nat} (hj : j < 512) : tabWord32 j < 2 ^ 32 := by
  have := (tabEntry_facts (i := 2 * j) (by omega)).2.2
  have := (tabEntry_facts (i := 2 * j + 1) (by omega)).2.2
  unfold tabWord32; omega

/-- Whether one of the first `n` entries divides the candidate. -/
def tr (n c : Nat) : Bool := (List.range n).any fun i => c % tabEntry i == 0

theorem tr_succ (n c : Nat) : tr (n + 1) c = (tr n c || decide (c % tabEntry n = 0)) := by
  simp only [tr, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  congr 1

theorem tr_trialAny (n c : Nat) : tr (4 * n) c = trialAny n c := rfl

theorem tr_mono_true {n k c : Nat} (le : n ≤ k) (found : tr n c = true) : tr k c = true := by
  unfold tr at found ⊢
  obtain ⟨j, member, divides⟩ := List.any_eq_true.mp found
  exact List.any_eq_true.mpr ⟨j, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp member) le), divides⟩

end VG.Proof.RsaKeyGen
