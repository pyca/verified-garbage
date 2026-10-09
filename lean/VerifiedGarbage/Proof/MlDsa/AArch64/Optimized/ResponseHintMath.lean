import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round

/-- Exact hint predicate, including the exceptional negative boundary at high zero. -/
abbrev hintPredicate (g : Nat) (t high : Int) : Prop :=
  (g:Int)<t ∨ t< -(g:Int) ∨ (t= -(g:Int) ∧ high≠0)

theorem hint_high_change {g : Nat} (hg : IsG g) (r : Zq) (c : Int)
    (hc : -4202495≤c ∧ c≤4210685) :
    highBits g (r+ofInt c)≠highBits g r ↔
      hintPredicate g (lowBits g r+c) (highBits g r) := by
  have h1 := hbF_le (mem_of_isG hg) r.isLt
  have h2 := hbF_le (mem_of_isG hg) (r+ofInt c).isLt
  simp only [highBits_eq (mem_of_isG hg),
    lowBits_eq (mem_of_isG hg)]
  have hv := VG.Proof.MlDsa.KeyGen.ofInt_val c
  have hr := r.isLt
  have hcq := (ofInt c).isLt
  simp only [VG.Proof.MlDsa.Round.val_add] at h2 ⊢
  have hadd : (r.val+(ofInt c).val)%q=if q≤r.val+(ofInt c).val then r.val+(ofInt c).val-q else r.val+(ofInt c).val := by
    have h : r.val+(ofInt c).val<2*q := by omega
    simp only [q] at *
    split <;> omega
  rw [hadd] at h2 ⊢
  have hgBound : g≤524288 := by rcases hg with rfl | rfl <;> decide
  have hm : c%8380417=if c<0 then c+8380417 else c := by
    simp only [q] at *
    split <;> omega
  rw [hm] at hv
  by_cases hn : hbF g (r+ofInt c).val=hbM g <;>
   rw [VG.Proof.MlDsa.Round.val_add,hadd] at hn <;>
   unfold hintPredicate <;>
   by_cases hf : hbF g r.val=hbM g <;>
   simp only [hf,ite_true,ite_false] <;>
   rcases hg with rfl | rfl <;>
    simp only [hbF,hbM,q,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88] at * <;>
    split at hv <;> split at h2 <;> simp_all only [ite_true,ite_false] <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
