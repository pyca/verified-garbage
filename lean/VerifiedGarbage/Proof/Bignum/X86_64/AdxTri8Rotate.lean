import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Row

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

/-- All triangular accumulators stay in registers untouched by addressing. -/
def Regs (rs : List Reg) : Prop := rs.Nodup ∧
  ∀ r ∈ rs, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx ∧ r≠.rdi

theorem rotate_regs {lo hi : Reg} {tail : List Reg} (h : Regs (lo::hi::tail)) : Regs (tail++[lo]) := by
  refine ⟨?_,?_⟩
  · rw [List.nodup_append]
    refine ⟨h.1.tail.tail,by simp,?_⟩
    intro r hr q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    subst q
    intro eq
    subst r
    exact (List.nodup_cons.mp h.1).1 (by simp [hr])
  · intro r hr
    apply h.2 r
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    rcases hr with hr | rfl
    · exact Or.inr (Or.inr hr)
    · exact Or.inl rfl

theorem rotate_subset {lo hi : Reg} {tail : List Reg} :
    ∀ r ∈ tail++[lo], r∈lo::hi::tail := by
  intro r hr
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
  rcases hr with hr | rfl
  · exact Or.inr (Or.inr hr)
  · exact Or.inl rfl

end VG.Proof.Bignum.X86_64.AdxTri8
