import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZDouble

/-! Copy the base point produced by DBLU into the shared-Z slots. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem co_ne {K : JacWinCfg} {size wk i j : Nat} (hL : Layout K size wk)
    (hj : j<18) (hne : i≠j) : coσ K i≠coσ K j := by
  intro he
  have hp := coP_readonly hL
  exact hne (getD_append_inj hL.nd hp (hp _ (List.mem_cons_self ..)) hj i he)

theorem copy_shared_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) (K.S.t2::K.S.t3::live K) E s) :
    WP isa (.block (copy 8 K.D.x K.S.t3++copy 8 K.D.y K.S.t2)) s fun t => ∃ E',
      ProgKeep K.M base wk [K.D.x,K.D.y] s t ∧
      Inv K.M base size C.p (·∈slots K) (K.D.y::K.D.x::K.S.t2::K.S.t3::live K) E' t ∧
      E' K.D.x=E K.S.t3 ∧ E' K.D.y=E K.S.t2 ∧ ∀ x∈live K,E' x=E x := by
  have dxy : K.D.x≠K.D.y := co_ne hL (i:=9) (j:=10) (by decide) (by decide)
  have tdx : K.S.t2≠K.D.x := co_ne hL (i:=2) (j:=9) (by decide) (by decide)
  have sep (x : Nat) (hx : x∈live K) : x≠K.D.x ∧ x≠K.D.y := by
    rcases List.mem_append.mp hx with hx|hx
    · constructor <;> intro he <;> apply hL.readonly x hx <;> rw [he] <;> simp [work]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      all_goals constructor
      all_goals first
        | exact co_ne hL (i:=12) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=12) (j:=10) (by decide) (by decide)
        | exact co_ne hL (i:=13) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=13) (j:=10) (by decide) (by decide)
        | exact co_ne hL (i:=14) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=14) (j:=10) (by decide) (by decide)
        | exact co_ne hL (i:=15) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=15) (j:=10) (by decide) (by decide)
        | exact co_ne hL (i:=16) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=16) (j:=10) (by decide) (by decide)
  rw [WP.block_append_iff]
  have n8 : 2*K.M.n=8 := by rw [hL.n]
  have first := copyField_ok hL.lay hW hi (o:=K.D.x) (by simp [slots,work])
    (a:=K.S.t3) (by simp)
  rw [n8] at first
  refine WP.mono first fun a ⟨ka,ia⟩ => ?_
  have second := copyField_ok hL.lay hW ia (o:=K.D.y) (by simp [slots,work])
    (a:=K.S.t2) (by simp)
  rw [n8] at second
  refine WP.mono second fun t ⟨kt,it⟩ => ⟨_,
    (progKeep_of_op ka (by simp)).trans (progKeep_of_op kt (by simp)),it,?_,?_,?_⟩
  · simp only [Function.update_apply,dxy,ite_false,ite_true]
  · simp only [Function.update_apply,tdx,ite_false,ite_true]
  · intro x hx
    simp only [Function.update_apply,(sep x hx).1,(sep x hx).2,ite_false]

end VG.Proof.Weierstrass.X86.JWin
