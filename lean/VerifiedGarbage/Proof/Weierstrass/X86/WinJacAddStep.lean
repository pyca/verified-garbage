import VerifiedGarbage.Proof.Weierstrass.X86.WinJacRepair
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacAddMath

/-! Cached addition and both branchless corrections for one signed digit. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem add_step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    {s₀ s : State} (h : Accum K C base size wk P k s₀
      (32*Window5.winE (k+16*Window5.geom K.J) K.J (j+1)) s)
    (he : Entry K C base (Window5.winPt C P (k+16*Window5.geom K.J) j) s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) (hj : j<K.J)
    (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0) :
    WP isa (.seq (fprog K.F K.addOps) (.block
      (nzMask 4 K.R.z++selPt 4 K.D K.E K.D++K.tc.digit++eqMask 0++selPt 4 K.R K.D K.R))) s fun t =>
      Accum K C base size wk P k s₀ (Window5.winE (k+16*Window5.geom K.J) K.J j) t ∧
      t.gpr .esi=BitVec.ofNat 32 j := by
  have hi := h.inv_entry hL hW hro he
  have hA := add_apart hL
  have sl : ∀ x∈(rcbW K.S K.D++rcbR K.S K.R K.E)++[K.z2,K.z3],x∈slots K := by
    intro x hx
    simp only [rcbW,rcbR,slots,ro,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hv : ∀ x∈rcbR K.S K.R K.E++[K.z2,K.z3],x∈(ro K++[K.R.x,K.R.y,K.R.z])++coords K := by
    intro x hx
    simp only [rcbR,ro,coords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  apply WP.seq
  refine WP.mono (cadd_ok hL.lay hW hm hA.1 hA.2.1 hA.2.2 sl hi hv he.z2 he.z3)
    fun a ⟨ka,ia,da⟩ => ?_
  have fa := h.frame.field hL hW ka (rcb_D_work K)
  have ba : ∀ i<260,a.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0 := by
    intro i hi; rw [fa.bits hL hi]; exact hb i hi
  have read (x : Nat) (hx : x∈rcbR K.S K.R K.E) :
      runOps K.addOps (tmv C K.M.n base s) x=tmv C K.M.n base s x :=
    value_after hL.lay hW hi ia ka (fun x hx => List.mem_append_right _ (rcb_D_work K x hx))
      (hv x (List.mem_append_left _ hx))
      (List.mem_append_right _ (hv x (List.mem_append_left _ hx))) (hA.1.apart x hx)
  have va : ∀ x∈jacCoords K.R++jacCoords K.D++jacCoords K.E,
      x∈[K.D.x,K.D.y,K.D.z]++((ro K++[K.R.x,K.R.y,K.R.z])++coords K) := by
    intro x hx
    simp only [jacCoords,coords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine WP.mono (repair_ok hL hW hm ia va (by have := hL.J; omega)
    ((ka.gpr _ (by decide)).trans hc) ba) fun t ⟨et,kt,it,vt⟩ => ?_
  have kw : ∀ x∈jacCoords K.D++jacCoords K.R,x∈work K := by
    intro x hx
    simp only [jacCoords,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine ⟨⟨fa.field hL hW kt kw,
    (h.table.field_keep hL h.frame.scr ka (rcb_D_work K) (by decide)).field_keep hL ia.scr kt kw (by decide),
    fun x hx => it.lt x (List.mem_append_left _ hx),?_⟩,
    (kt.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hc)⟩
  intro hk
  apply it.point_tmv (fun _ hx => List.mem_append_left _ hx)
  change (fun q : Fe C × Fe C × Fe C => InvJ C q.1 q.2.1 q.2.2
    (mul (Window5.winE (k+16*Window5.geom K.J) K.J j) P)) (et K.R.x,et K.R.y,et K.R.z)
  rw [vt,read _ (by simp [rcbR]),read _ (by simp [rcbR]),read _ (by simp [rcbR]),
    read _ (by simp [rcbR]),read _ (by simp [rcbR]),read _ (by simp [rcbR]),da]
  exact add_result_ok hC ha hO hP hP0 hn17 hn64 hk hj (h.point hk) he.jac

end VG.Proof.Weierstrass.X86.JWin
