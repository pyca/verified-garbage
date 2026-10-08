import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! The two cached powers of a Jacobian table entry. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem cache_ok {K : JacWinCfg} {base : Addr} {size wk m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hW : WkOk K.F K.M m size wk Sl)
    (hm : UnitMod m (2^(64*K.M.n))) (hSl : ∀ x∈[K.E.z,K.z2,K.z3],Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl V E s)
    (hV : K.E.z∈V) :
    WP isa (fprog K.F K.cacheOps) s fun t =>
      ProgKeep K.M base wk [K.z2,K.z3] s t ∧
      Inv K.M base size m Sl ([K.z2,K.z3]++V) (runOps K.cacheOps E) t ∧
      (∀ x,x≠K.z2 → x≠K.z3 → runOps K.cacheOps E x=E x) ∧
      runOps K.cacheOps E K.z2=E K.E.z*E K.E.z ∧
      runOps K.cacheOps E K.z3=runOps K.cacheOps E K.z2*E K.E.z := by
  have h2 : K.E.z≠K.z2 := by simp only [JacWinCfg.E,JacWinCfg.z2]; omega
  have h3 : K.E.z≠K.z3 := by simp only [JacWinCfg.E,JacWinCfg.z3]; omega
  have h23 : K.z2≠K.z3 := by simp only [JacWinCfg.z2,JacWinCfg.z3]; omega
  have hs : ∀ op∈K.cacheOps,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    simp only [JacWinCfg.cacheOps,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx <;>
      rcases hx with rfl|rfl|rfl <;> exact hSl _ (by simp)
  have hr : readsOk K.cacheOps V=true := by simp [JacWinCfg.cacheOps,readsOk,FOp.ins,FOp.out,hV]
  refine WP.mono (fprog_ok hL hW hm _ hI hs hr) fun t ⟨kt,it⟩ =>
    ⟨kt.mono (by intro x hx; simpa [JacWinCfg.cacheOps,FOp.out] using hx),it.sub ?_,?_,?_,?_⟩
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · right
      simpa [JacWinCfg.cacheOps,FOp.out] using hx
    · exact Or.inl hx
  · intro x hx2 hx3
    simp only [JacWinCfg.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
      Function.update_apply,hx2,hx3,ite_false]
  · simp only [JacWinCfg.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
      Function.update_apply,h2,h23,ite_false,ite_true]
  · simp only [JacWinCfg.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
      Function.update_apply,h2,h23,ite_false,ite_true]

end VG.Proof.Weierstrass.X86.JWin
