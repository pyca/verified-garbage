import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildMixed

/-! Copy the two input coordinates required by the mixed-addition schedule. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem mixed_copy_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (·∈slots K) (live K) E s) :
    WP isa (.block (copy 8 K.S.t2 K.E.x++copy 8 K.S.t4 K.E.y)) s fun t => ∃ E',
      ProgKeep K.M base wk [K.S.t2,K.S.t4] s t ∧
      Inv K.M base size C.p (·∈slots K) (K.S.t4::K.S.t2::live K) E' t ∧
      E' K.S.t2=E' K.E.x ∧ E' K.S.t4=E' K.E.y ∧ (∀ x∈live K,E' x=E x) := by
  have nd : ([K.S.t2,K.S.t4,K.E.x,K.E.y,K.E.z] : List Nat).Nodup := by
    apply List.Nodup.sublist (l₂:=rcbW K.S K.E) _ (rcb_E_nd hL)
    simp only [rcbW]
    repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd
  have sep (x : Nat) (hx : x∈live K) : x≠K.S.t2 ∧ x≠K.S.t4 := by
    have nd' := hL.nd
    simp only [work,temps,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd'
    rcases List.mem_append.mp hx with hx|hx
    · constructor <;> intro he <;> apply hL.readonly x hx <;> rw [he] <;> simp [work,temps]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> grind
  rw [WP.block_append_iff]
  have n8 : 2*K.M.n=8 := by rw [hL.n]
  have first := copyField_ok hL.lay hW hI (o:=K.S.t2) (by simp [slots,work,temps])
    (a:=K.E.x) (by simp [live])
  rw [n8] at first
  refine WP.mono first fun a ⟨ka,ia⟩ => ?_
  have second := copyField_ok hL.lay hW ia (o:=K.S.t4) (by simp [slots,work,temps])
    (a:=K.E.y) (by simp [live])
  rw [n8] at second
  refine WP.mono second fun t ⟨kt,it⟩ => ⟨_,
    (progKeep_of_op ka (by simp)).trans (progKeep_of_op kt (by simp)),it,?_,?_,?_⟩
  · simp only [Function.update_apply]
    simp (disch := grind) only [ite_eq_right,ite_true]
  · simp only [Function.update_apply]
    simp (disch := grind) only [ite_eq_right,ite_true]
  · intro x hx
    simp only [Function.update_apply,(sep x hx).1,(sep x hx).2,ite_false]

end VG.Proof.Weierstrass.X86.JWin
