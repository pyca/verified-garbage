module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! Ordinary range and equality checks cannot overwrite the retained comb table. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.Proof.Mont VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic

theorem canonical_outs {n e p g : Nat} {base : Addr} {m m' : Mem} {rs : List (Nat × Nat)}
    (h : Supported n e) (C : canonical n e p g base m) (O : Outs base rs m m')
    (apart : ∀ r∈rs, context n+8*Proof.Dsa.FixedBaseComb.contextWords (layout n e)≤r.1 ∨
      r.1+r.2≤context n) : canonical n e p g base m' := by
  unfold canonical at C ⊢
  rw [wordsAt_canonical,wordsVal_eq_val32,
    O.val32 (by simpa only [←Nat.mul_assoc] using apart) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),
    ←wordsVal_eq_val32,←wordsAt_canonical]
  exact C

theorem canonical_check {n e k p g : Nat} {base : Addr} {m m' : Mem}
    (h : Supported n e) (hk : k≤48) (C : canonical n e p g base m)
    (O : Outs base [(0,contextBytes k),(VG.Impl.Dsa.X86.Layout.field .mask,4)] m m') :
    canonical n e p g base m' := by
  apply canonical_outs h C O
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · have B := VG.Proof.Dsa.X86.Layout.context_bound hk
    change contextBytes k≤7048 at B
    apply Or.inr
    simp only [Nat.zero_add]
    unfold context; split <;> omega
  · apply Or.inr
    change 8248≤context n
    unfold context; split <;> omega

end VG.Proof.Dsa.X86.Comb
