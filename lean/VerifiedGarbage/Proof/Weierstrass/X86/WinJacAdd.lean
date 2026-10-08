import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.CachedJacField

/-! The secret-scalar loop's cached-power Jacobian addition. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem cadd_ok {K : JacWinCfg} {base : Addr} {size wk m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hW : WkOk K.F K.M m size wk Sl)
    (hm : UnitMod m (2^(64*K.M.n))) (hA : RcbApart K.S K.R K.E K.D)
    (h2a : K.z2∉rcbW K.S K.D) (h3a : K.z3∉rcbW K.S K.D)
    (hSl : ∀ x∈(rcbW K.S K.D++rcbR K.S K.R K.E)++[K.z2,K.z3],Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl V E s)
    (hV : ∀ x∈rcbR K.S K.R K.E++[K.z2,K.z3],x∈V)
    (h2 : E K.z2=E K.E.z*E K.E.z) (h3 : E K.z3=E K.z2*E K.E.z) :
    WP isa (fprog K.F K.addOps) s fun t =>
      ProgKeep K.M base wk (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl ([K.D.x,K.D.y,K.D.z]++V) (runOps K.addOps E) t ∧
      (runOps K.addOps E K.D.x,runOps K.addOps E K.D.y,runOps K.addOps E K.D.z)=
        jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have e3 : K.z2+8*4=K.z3 := by simp only [JacWinCfg.z2,JacWinCfg.z3,Nat.add_assoc]
  have eqops : K.addOps=(CachedJac.headN++jacTailN).map
      (FOp.rename (CachedJac.rename 4 K.S K.R K.E K.D K.z2)) := by
    rw [JacWinCfg.addOps,JacWinCfg.addHead,CachedJac.head_eq 4 K.S K.R K.E K.D K.z2,
      CachedJac.tail_eq 4 K.S K.R K.E K.D K.z2,List.map_append]
  have hr : readsOk K.addOps V=true := by
    rw [eqops]
    refine readsOk_mono (readsOk_rename (CachedJac.rename 4 K.S K.R K.E K.D K.z2)
      (show readsOk (CachedJac.headN++jacTailN) [9,10,11,12,13,14,15,16,17,18]=true by decide)) ?_
    simpa [CachedJac.rename,rcbσ,rcbW,rcbR,e3] using hV
  have hs : ∀ op∈K.addOps,∀ x∈op.out::op.ins,Sl x := by
    rw [eqops]
    intro op hop x hx
    apply hSl x
    simpa only [e3] using CachedJac.slots op hop x hx
  refine WP.mono (fprog_ok hL hW hm _ hI hs hr) fun t ⟨kt,it⟩ => ⟨kt.mono ?_,it.sub ?_,?_⟩
  · intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    rw [eqops] at hop
    exact CachedJac.out (show ∀ op∈CachedJac.headN++jacTailN,op.out<9 by decide) hop
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [JacWinCfg.addOps,jacTail,FOp.out]
    · exact Or.inl hx
  · exact CachedJac.full_run hA h2a (by rw [e3]; exact h3a) E h2 (by rw [e3]; exact h3)

end VG.Proof.Weierstrass.X86.JWin
