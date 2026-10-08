import VerifiedGarbage.Proof.Weierstrass.X86.WinJacDouble
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuild

/-! The accumulator keeps canonical fields even for scalars later rejected by ECDH. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure Accum (K : JacWinCfg) (C : Curve) (base : Addr) (size wk : Nat)
    (P : Point C) (k : Nat) (s₀ : State) (e : Nat) (s : State) : Prop where
  frame : Frame K C base size wk s₀ s
  table : Table K C base P 16 s
  lt : ∀ x∈[K.R.x,K.R.y,K.R.z],wordsVal s.mem base x K.M.n<C.p
  point : k<C.n → InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul e P)

theorem Accum.keeps {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    {P : Point C} {s₀ s t : State} (h : Accum K C base size wk P k s₀ e s) (hk : CKeeps [.esi] s t) :
    Accum K C base size wk P k s₀ e t := by
  refine ⟨h.frame.keeps hk,?_,?_,?_⟩
  · intro m h1 hm; exact (h.table m h1 hm).congr fun _ _ => by rw [hk.2.1]
  · rw [hk.2.1]; exact h.lt
  · simpa only [tmv,hk.2.1] using h.point

theorem rcb_R_work (K : JacWinCfg) : ∀ x∈rcbW K.S K.R,x∈work K := by
  intro x hx
  simp only [rcbW,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem rcb_R_nd {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    (rcbW K.S K.R).Nodup := by
  apply List.Nodup.sublist (l₂:=work K) _ hL.nd
  simp only [rcbW,work,temps,List.cons_append,List.nil_append]
  repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

theorem Accum.inv {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    {P : Point C} {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) :
    Inv K.M base size C.p (·∈slots K) (ro K++[K.R.x,K.R.y,K.R.z]) (tmv C K.M.n base s) s := by
  refine ⟨h.frame.scr,h.frame.mod,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [slots,work]
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · rw [h.frame.ro hL hW hx]; exact hro x hx
    · exact h.lt x hx

theorem Accum.preserve {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    {P : Point C} {s₀ s t : State} (h : Accum K C base size wk P k s₀ e s)
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {W : List Nat} (hk : ProgKeep K.M base wk W s t) (hw : ∀ x∈W,x∈work K)
    (hd : ∀ x∈[K.R.x,K.R.y,K.R.z],x∉W) : Accum K C base size wk P k s₀ e t := by
  have hs : ∀ x∈[K.R.x,K.R.y,K.R.z],x∈slots K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [slots,work]
  refine ⟨h.frame.field hL hW hk hw,h.table.field_keep hL h.frame.scr hk hw (by decide),?_,?_⟩
  · intro x hx
    rw [hk.slot hL.lay hW h.frame.scr (fun x hx => List.mem_append_right _ (hw x hx)) (hs x hx) (hd x hx)]
    exact h.lt x hx
  · intro hvalid
    exact hk.invJ hL.lay hW h.frame.scr (fun x hx => List.mem_append_right _ (hw x hx)) hs hd (h.point hvalid)

theorem double_accum_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) :
    WP isa (K.dbl K.R) s fun t => Accum K C base size wk P k s₀ (2*e) t ∧
      ProgKeep K.M base wk (rcbW K.S K.R) s t := by
  have hi := h.inv hL hW hro
  refine WP.mono (dbl_field_ok hL.lay hW hm (rcb_R_nd hL)
    (fun hx => hL.readonly K.S.a (by simp [ro]) (rcb_R_work K _ hx))
    (fun x hx => List.mem_append_right _ (rcb_R_work K x hx)) hi
    (fun _ hx => List.mem_append_right _ hx)) fun t ⟨kt,it,et⟩ => ?_
  refine ⟨⟨h.frame.field hL hW kt (rcb_R_work K),h.table.field_keep hL h.frame.scr kt (rcb_R_work K)
    (by decide),fun x hx => it.lt x (List.mem_append_left _ hx),?_⟩,kt⟩
  intro hk
  have jt := InvJ.dbl' hC ha (hC.onCurve_mul hP e) (h.point hk) et
  rw [hC.add_mul_mul hP,show e+e=2*e by omega] at jt
  exact it.point_tmv (fun _ hx => List.mem_append_left _ hx) jt

end VG.Proof.Weierstrass.X86.JWin
