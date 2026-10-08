import VerifiedGarbage.Proof.Weierstrass.X86.WinJacEntry

/-! Preserve the accumulator while selecting and signing a table entry. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem entry_nd {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    (coords K++[K.neg]).Nodup := by
  apply List.Nodup.sublist (l₂:=work K) _ hL.nd
  simp only [coords,work,temps,List.cons_append,List.nil_append]
  repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

theorem entry_apart_R {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    ∀ x∈[K.R.x,K.R.y,K.R.z],x∉coords K++[K.neg] := by
  have hn : ([K.R.x,K.R.y,K.R.z]++coords K++[K.neg]).Nodup := by
    apply List.Nodup.sublist (l₂:=work K) _ hL.nd
    simp only [coords,work,temps,List.cons_append,List.nil_append]
    repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons
  rw [List.append_assoc,List.nodup_append] at hn
  exact fun x hx hy => hn.2.2 x hx x hy rfl

theorem Accum.inv_entry {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    {P Q : Point C} {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) (he : Entry K C base Q s) :
    Inv K.M base size C.p (·∈slots K) ((ro K++[K.R.x,K.R.y,K.R.z])++coords K) (tmv C K.M.n base s) s := by
  have hi := h.inv hL hW hro
  refine ⟨hi.scr,hi.mod,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hi.sl x hx
    · exact List.mem_append_right _ (coords_work K x hx)
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hi.lt x hx
    · exact he.lt x hx

theorem Frame.inv_entry {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {Q : Point C} {s₀ s : State} (h : Frame K C base size wk s₀ s)
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hro : ∀ x∈JWin.ro K,wordsVal s₀.mem base x K.M.n<C.p) (he : Entry K C base Q s) :
    Inv K.M base size C.p (·∈slots K) (JWin.ro K++coords K) (tmv C K.M.n base s) s := by
  refine ⟨h.scr,h.mod,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (coords_work K x hx)
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · rw [h.ro hL hW hx]; exact hro x hx
    · exact he.lt x hx

end VG.Proof.Weierstrass.X86.JWin
