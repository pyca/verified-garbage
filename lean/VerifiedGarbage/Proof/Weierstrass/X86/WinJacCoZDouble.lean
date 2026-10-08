import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZState

/-! DBLU constructs the second entry and the rescaled base point. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem dblu_point_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈[K.P.x,K.P.y,K.P.z],x∈V)
    (hj : InvJ C (E K.P.x) (E K.P.y) 1 P) (hz : E K.P.z=1) :
    WP isa (fprog K.F K.dbluOps) s fun t =>
      ProgKeep K.M base wk (work K) s t ∧
      Cached C base t (fun c => K.T+32*c) (mul 2 P) ∧
      wordsVal t.mem base K.S.t2 K.M.n<C.p ∧ wordsVal t.mem base K.S.t3 K.M.n<C.p ∧
      InvJ C (tmv C K.M.n base t K.S.t3) (tmv C K.M.n base t K.S.t2)
        (tmv C K.M.n base t K.E.z) P := by
  have hr : readsOk (dbluN.map (FOp.rename (coσ K))) V=true :=
    readsOk_mono (readsOk_rename (coσ K) dbluN_reads) fun x hx => hV x (by
      simpa only [List.map_cons,List.map_nil,coσ,work,temps,List.cons_append,List.nil_append,
        List.getD_cons_zero,List.getD_cons_succ] using hx)
  rw [dblu_eq]
  refine WP.mono (coProg_ok hL hW hm dbluN_out hi hr) fun t ⟨kt,it,hv⟩ => ?_
  have hz' : E (coσ K 20)=1 := hz
  obtain ⟨jt,h2,h3,hx,hy⟩ := dbluN_run (fun i => E (coσ K i)) hz'
  generalize runOps dbluN (fun i => E (coσ K i))=r at hv jt h2 h3 hx hy
  have jp : InvJ C (E (coσ K 18)) (E (coσ K 19)) 1 P := hj
  have j2 := InvJ.dbl' hC ha hP jp jt
  have he : Spec.Weierstrass.add P P=mul 2 P := by
    simpa only [mul_one_pt] using hC.add_mul_mul hP 1 1
  rw [he] at j2
  have z : r 14≠0 := fun h => Window5.mul_ne_infinity hO hP hP0 (m:=2)
    (by decide) (by omega) ((j2.z_zero_iff hC).mp h)
  have jd : InvJ C (r 3) (r 2) (r 14) P := jp.rescale hC z hC.one_ne_zero hx hy (by grind)
  have value (i : Nat) (ho : i∈dbluN.map FOp.out) : tmv C K.M.n base t (coσ K i)=r i :=
    (it.val _ (co_valid ho)).trans (hv i)
  refine ⟨kt,co_cached hL.n it hv (by
    have hb : ∀ i<17,12≤i → i∈dbluN.map FOp.out := by decide
    exact fun i h12 h16 => hb i (by omega) h12) j2 z h2 h3,
    it.lt _ (co_valid (i:=2) (by decide)),it.lt _ (co_valid (i:=3) (by decide)),?_⟩
  have v3 : tmv C K.M.n base t K.S.t3=r 3 := value 3 (by decide)
  have v2 : tmv C K.M.n base t K.S.t2=r 2 := value 2 (by decide)
  have v14 : tmv C K.M.n base t K.E.z=r 14 := value 14 (by decide)
  rw [v3,v2,v14]
  exact jd

end VG.Proof.Weierstrass.X86.JWin
