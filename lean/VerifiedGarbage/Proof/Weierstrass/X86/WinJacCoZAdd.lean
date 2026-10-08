import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZState

/-! ZADDU advances the table while retaining a base point with the sum's Z. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem zaddu_point_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    (h2 : 2≤m) (h15 : m≤15) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈[K.D.x,K.D.y,K.E.x,K.E.y,K.E.z,K.z2],x∈V)
    (hD : InvJ C (E K.D.x) (E K.D.y) (E K.E.z) P)
    (hT : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) (mul m P))
    (hz : E K.E.z≠0) (hpow : E K.z2=E K.E.z*E K.E.z) :
    WP isa (fprog K.F K.zadduOps) s fun t =>
      ProgKeep K.M base wk (work K) s t ∧
      Cached C base t (fun c => K.T+32*c) (mul (m+1) P) ∧ SharedZ K C base P t := by
  have hr : readsOk (zadduN.map (FOp.rename (coσ K))) V=true :=
    readsOk_mono (readsOk_rename (coσ K) zadduN_reads) fun x hx => hV x (by
      simpa only [List.map_cons,List.map_nil,coσ,work,temps,List.cons_append,List.nil_append,
        List.getD_cons_zero,List.getD_cons_succ] using hx)
  rw [zaddu_eq]
  refine WP.mono (coProg_ok hL hW hm zadduN_out hi hr) fun t ⟨kt,it,hv⟩ => ?_
  obtain ⟨jt,hz2,hz3⟩ := zadduN_run (fun i => E (coσ K i))
  generalize runOps zadduN (fun i => E (coσ K i))=r at hv jt hz2 hz3
  have hx := zaddu_x hC hO hP hP0 hn h2 h15 hD hT hz
  have js := InvJ.zaddu hC ha hP (hC.onCurve_mul hP m) hD hT hz hx
  have jt' : ((r 12,r 13,r 14),(r 9,r 10))=zadduF (E K.D.x) (E K.D.y)
      (E K.E.x) (E K.E.y) (E K.E.z) := jt
  rw [←jt'] at js
  have he : Spec.Weierstrass.add (mul m P) P=mul (m+1) P :=
    (congrArg (Spec.Weierstrass.add (mul m P)) (mul_one_pt P).symm).trans (hC.add_mul_mul hP m 1)
  rw [he] at js
  have z : r 14≠0 := fun h => Window5.mul_ne_infinity hO hP hP0 (m:=m+1)
    (by omega) (by omega) ((js.1.z_zero_iff hC).mp h)
  have value (i : Nat) (ho : i∈zadduN.map FOp.out) : tmv C K.M.n base t (coσ K i)=r i :=
    (it.val _ (co_valid ho)).trans (hv i)
  refine ⟨kt,co_cached hL.n it hv (by
    have hb : ∀ i<17,12≤i → i∈zadduN.map FOp.out := by decide
    exact fun i h12 h16 => hb i (by omega) h12) js.1 z (hz2 hpow) hz3,?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact it.lt _ (co_valid (i:=9) (by decide))
    · exact it.lt _ (co_valid (i:=10) (by decide))
  · have v9 : tmv C K.M.n base t K.D.x=r 9 := value 9 (by decide)
    have v10 : tmv C K.M.n base t K.D.y=r 10 := value 10 (by decide)
    have v14 : tmv C K.M.n base t K.E.z=r 14 := value 14 (by decide)
    rw [v9,v10,v14]
    exact js.2

end VG.Proof.Weierstrass.X86.JWin
