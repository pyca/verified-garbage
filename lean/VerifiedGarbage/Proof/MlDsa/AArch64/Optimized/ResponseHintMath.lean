import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round

/-- Exact hint predicate, including the exceptional negative boundary at high zero. -/
abbrev hintPredicate (g : Nat) (t high : Int) : Prop :=
  (g:Int)<t ∨ t< -(g:Int) ∨ (t= -(g:Int) ∧ high≠0)

/-- `f mod m`, without the modulus: `f ≤ m`. -/
theorem hbF_mod_hbM {g a : Nat} (hg : IsG g) (ha : a < q) :
    hbF g a % hbM g = if hbF g a = hbM g then 0 else hbF g a := by
  split
  · rename_i h; rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_ne (hbF_le (mem_of_isG hg) ha) ‹_›)

/-- By cases on whether `r` and `r + c` are at the top of their range (`f = m`), for
each `γ₂`, the sign of `c` and the carry of `r + c` past `q`: with no `%` left,
`omega` decides each case on a few linear facts. -/
theorem hint_high_change {g : Nat} (hg : IsG g) (r : Zq) (c : Int)
    (hc : -4202495≤c ∧ c≤4210685) :
    highBits g (r+ofInt c)≠highBits g r ↔
      hintPredicate g (lowBits g r+c) (highBits g r) := by
  have hgm := mem_of_isG hg
  rw [highBits_eq hgm, highBits_eq hgm, lowBits_eq hgm, VG.Proof.MlDsa.Round.val_add,
    hbF_mod_hbM hg r.isLt, hbF_mod_hbM hg (Nat.mod_lt _ (by decide))]
  have hv := VG.Proof.MlDsa.KeyGen.ofInt_val c
  have hr := r.isLt
  have hx := (ofInt c).isLt
  generalize r.val = a at *
  generalize (ofInt c).val = x at *
  unfold hintPredicate
  by_cases hf : hbF g a = hbM g <;> simp only [hf, ite_true, ite_false] <;>
  by_cases hn : hbF g ((a + x) % q) = hbM g <;> simp only [hn, ite_true, ite_false] <;>
  rcases hg with rfl | rfl <;>
    simp only [hbF, hbM, q, Impl.MlDsa.AArch64.Round.g32, Impl.MlDsa.AArch64.Round.g88, Nat.reduceMul,
      Nat.reduceSub, Nat.reduceDiv] at * <;>
    simp (disch := decide) only [Nat.add_sub_assoc, Nat.reduceSub] at * <;>
    rcases Int.lt_or_le c 0 with hc0 | hc0 <;> rcases Nat.lt_or_ge (a + x) 8380417 with hs | hs <;>
    (first | rw [Nat.mod_eq_of_lt hs] at * | rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)] at *) <;>
    omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
