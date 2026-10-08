import VerifiedGarbage.Proof.Weierstrass.X86.WinJacNeg

/-! Seed the accumulator from the top signed digit, avoiding five doublings. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem first_value {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P=true)
    {v J : Nat} (hJ : 1≤J) (hlo : 16*Window5.geom J≤v) (hhi : v<32^J) :
    Window5.winPt C P v (J-1)=mul (Window5.winE v J (J-1)) P := by
  have he := Window5.win_add hC hP hlo (show J-1<J by omega)
  rw [show J-1+1=J by omega,Window5.winE_top hhi,Nat.mul_zero,Window5.mul_zero_pt] at he
  exact he

theorem first_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k v : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) {P : Point C} (hP : onCurve C P=true)
    {s₀ s : State} (hf : Frame K C base size wk s₀ s) (ht : Table K C base P 16 s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if v.testBit i then 1 else 0)
    (hlo : 16*Window5.geom K.J≤v) (hhi : v<32^K.J) :
    WP isa K.first s fun t => Accum K C base size wk P k s₀ (Window5.winE v K.J (K.J-1)) t ∧
      t.gpr .esi=BitVec.ofNat 32 (K.J-1) := by
  unfold JacWinCfg.first
  apply WP.seq
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (mov_counter_ok s (K.J-1)) fun a ⟨ca,ka⟩ => ?_
  have fa := hf.keeps ka
  have ta : Table K C base P 16 a := fun m h1 hm => (ht m h1 hm).congr fun _ _ => by rw [ka.2.1]
  have hj : K.J-1<52 := by have := hL.J; omega
  refine WP.mono (read_fields_ok hL hW fa ta hj ca hb) fun b ⟨pb,kb,cb⟩ => ?_
  have fb := fa.field hL hW kb (coords_work K)
  have tb := ta.field_keep hL fa.scr kb (coords_work K) (by decide)
  apply WP.seq
  refine WP.mono (neg_fields_ok hL hW hm fb pb hro hz hj cb hb) fun c ⟨pc,kc,cc⟩ => ?_
  have nw : ∀ x∈[K.neg,K.E.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  have fc := fb.field hL hW kc nw
  have tc := tb.field_keep hL fb.scr kc nw (by decide)
  have ic := fc.inv_entry hL hW hro pc
  have hn : (jacCoords K.R).Nodup := by
    apply List.Nodup.sublist (l₂:=rcbW K.S K.R) _ (rcb_R_nd hL)
    simp only [jacCoords,rcbW]
    repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons
  have rwk : ∀ x∈jacCoords K.R,x∈work K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [work]
  have ev : ∀ x∈jacCoords K.E,x∈ro K++coords K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [coords]
  have sep : ∀ x∈jacCoords K.E,∀ y∈jacCoords K.R,x≠y := by
    intro x hx y hy he
    apply entry_apart_R hL y hy
    rw [←he]
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [coords]
  rw [←hL.n]
  refine WP.mono (copyPointFields_ok hL.lay hW hn sep
    (fun x hx => List.mem_append_right _ (rwk x hx)) ic ev) fun t ⟨et,kt,it,vt⟩ => ?_
  refine ⟨⟨fc.field hL hW kt rwk,tc.field_keep hL fc.scr kt rwk (by decide),
    fun x hx => it.lt x (List.mem_append_left _ hx),?_⟩,(kt.gpr _ (by decide)).trans cc⟩
  intro _
  apply it.point_tmv (fun _ hx => List.mem_append_left _ hx)
  simp only [Prod.mk.injEq] at vt
  rw [vt.1,vt.2.1,vt.2.2]
  have jp := pc.jac
  have he : (if Window5.nib v (K.J-1)<16 then negPt (mul (magH 16 (Window5.nib v (K.J-1))) P)
      else mul (magH 16 (Window5.nib v (K.J-1))) P)=Window5.winPt C P v (K.J-1) := by
    simpa using (Window5.winPt_mag P v (K.J-1)).symm
  rw [he,first_value hC hP (by have := hL.J; omega) hlo hhi] at jp
  exact jp

end VG.Proof.Weierstrass.X86.JWin
