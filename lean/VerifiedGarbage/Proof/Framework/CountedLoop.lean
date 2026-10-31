module

public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Counted loops with a fixed positive step -/

@[expose] public section
namespace VG

/-- Both data loops decrease the number of remaining blocks by a fixed positive chunk. -/
theorem WP.chunk_loop {M : ISA} {I : Nat → M.State → Prop} {n N k : Nat} {s : M.State} {body : Prog M} {cond : M.Cond}
    (hN : 0 < N) (hk : k+N ≤ n) (hs : I k s)
    (step : ∀ k t, k+N ≤ n → I k t → WP M body t (I (k+N)))
    (test : ∀ k t, k ≤ n → I k t →
      (n-k < N → M.eval cond t = some false) ∧ (N ≤ n-k → M.eval cond t = some true)) :
    WP M (.loop body cond) s fun t => ∃ j, j ≤ n ∧ n-j < N ∧ I j t := by
  let J : Nat → M.State → Prop := fun m t => ∃ j, m = n-j ∧ j+N ≤ n ∧ I j t
  have advance : ∀ m t, J m t → WP M body t fun u =>
      (M.eval cond u = some false ∧ ∃ j, j ≤ n ∧ n-j < N ∧ I j u) ∨
      (M.eval cond u = some true ∧ ∃ m' < m, J m' u) := by
    rintro m t ⟨j, rfl, hj, ht⟩
    refine WP.mono (step j t hj ht) fun u hu => ?_
    have he := test (j+N) u hj hu
    by_cases hl : n-(j+N) < N
    · exact Or.inl ⟨he.1 hl, j+N, hj, hl, hu⟩
    · exact Or.inr ⟨he.2 (by omega), n-(j+N), by omega, j+N, rfl, by omega, hu⟩
  exact WP.loop (M := M) J advance (n-k) s ⟨k, rfl, hk, hs⟩

end VG
