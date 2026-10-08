import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildPrep

/-! One mixed-addition table entry, including its copies and frame. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem build_arith_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    (h2 : 2≤m) (h15 : m≤15) {s₀ s : State} (hf : Frame K C base size wk s₀ s)
    (ht : Table K C base P m s) (hp : Cached C base s (fun c => K.T+32*c) (mul m P))
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hJP : InvJ C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) 1 P) :
    WP isa (.seq (.block (copy 8 K.S.t2 K.E.x++copy 8 K.S.t4 K.E.y))
      (fprog K.F (K.maddOps++K.cacheOps))) s fun t =>
      Cached C base t (fun c => K.T+32*c) (mul (m+1) P) ∧
      Frame K C base size wk s₀ t ∧ Table K C base P m t ∧
      ProgKeep K.M base wk (rcbW K.S K.E++[K.z2,K.z3]) s t := by
  have hi := hf.inv_cached hL hW hro hp
  apply WP.seq
  refine WP.mono (mixed_copy_ok hL hW hi) fun a ⟨ea,ka,ia,et2,et4,ea_eq⟩ => ?_
  have hv : ∀ x∈[K.S.t2,K.S.t4,K.E.x,K.E.y,K.E.z,K.P.x,K.P.y],x∈K.S.t4::K.S.t2::live K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [live,ro]
  have ej : InvJ C (ea K.E.x) (ea K.E.y) (ea K.E.z) (mul m P) := by
    rw [ea_eq _ (by simp [live]),ea_eq _ (by simp [live]),ea_eq _ (by simp [live]),hL.n]
    exact hp.jac
  have ep (x : Nat) (hx : x∈ro K) : ea x=tmv C K.M.n base s₀ x := by
    rw [ea_eq x (List.mem_append_left _ hx)]
    unfold tmv
    rw [hf.ro hL hW hx]
  have jp : InvJ C (ea K.P.x) (ea K.P.y) 1 P := by
    rw [ep _ (by simp [ro]),ep _ (by simp [ro])]
    exact hJP
  have hz : ea K.E.z≠0 := by
    rw [ea_eq _ (by simp [live]),hL.n]
    exact hp.z
  have noexc := Window5.tbl_noexc hC hO hP hP0 hn h2 h15
  refine WP.mono (mixed_point_ok hL hW hm hC ha ia hv et2 et4 hP (hC.onCurve_mul hP m)
    ej jp hz noexc.1 noexc.2) fun t ⟨pt,kt⟩ => ?_
  have kaw : ∀ x∈[K.S.t2,K.S.t4],x∈rcbW K.S K.E++[K.z2,K.z3] := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [rcbW]
  have kk := (ka.mono kaw).trans kt
  refine ⟨?_,hf.field hL hW kk (mixed_work K),ht.field_keep hL hf.scr kk (mixed_work K) (by omega),kk⟩
  have he : Spec.Weierstrass.add (mul m P) P=mul (m+1) P := by
    exact (congrArg (Spec.Weierstrass.add (mul m P)) (mul_one_pt P).symm).trans
      (hC.add_mul_mul hP m 1)
  rw [he] at pt
  exact pt

end VG.Proof.Weierstrass.X86.JWin
