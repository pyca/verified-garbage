import VerifiedGarbage.Proof.Weierstrass.X86.NafTableState

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

theorem nafCopyStore_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size m wk : Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hm : m<8) 
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈nafSlots K) V E s)
    (hV : ∀ x∈jacCoords K.D,x∈V) (hc : s.gpr .esi=BitVec.ofNat 32 m)
    {P : Point C} (hp : InvJ C (E K.D.x) (E K.D.y) (E K.D.z) P) :
    WP isa (.block (copyPt 4 K.R K.D++Naf.tableStore K)) s fun t =>
      ProgKeep K.M base wk (jacCoords K.R++jacCoords (K.tblPt (m+1))) s t ∧
      Inv K.M base size C.p (·∈nafSlots K) (jacCoords (K.tblPt (m+1))++jacCoords K.R++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y) (tmv C K.M.n base t K.R.z) P ∧
      InvJ C (tmv C K.M.n base t (K.tblPt (m+1)).x) (tmv C K.M.n base t (K.tblPt (m+1)).y)
        (tmv C K.M.n base t (K.tblPt (m+1)).z) P := by
  have rr : ∀ x∈jacCoords K.R,x∈winOther K := by
    intro x hx
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := fun x hx =>
    List.mem_append_left _ (List.mem_append_right _ (rr x hx))
  have hA := hL.rcbApart_DR
  have hN : (jacCoords K.R).Nodup := hA.nodup.drop (i:=6)
  have hqa : ∀ x∈jacCoords K.D,∀ y∈jacCoords K.R,x≠y := by
    intro x hx y hy he
    apply hA.apart x (by
      simp only [jacCoords,rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind)
    rw [he]
    simp only [jacCoords,rcbW,List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
    grind
  have sep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x := by
    have hx := hL.tbl K.R.x (List.mem_append_right _ (rr _ (by simp [jacCoords])))
    have hz := hL.tbl K.R.z (List.mem_append_right _ (rr _ (by simp [jacCoords])))
    rw [hL.rxz] at hz
    omega
  rw [WP.block_append_iff,←hL.n]
  refine WP.mono (copyPointFields_ok hL.lay hAcc hN hqa rs hI hV) fun a ⟨ea,ka,ia,va⟩ => ?_
  have ja : InvJ C (tmv C K.M.n base a K.R.x) (tmv C K.M.n base a K.R.y) (tmv C K.M.n base a K.R.z) P := by
    apply ia.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at va
    rw [va.1,va.2.1,va.2.2]
    exact hp
  have ca : a.gpr .esi=BitVec.ofNat 32 m := (ka.gpr _ (by decide)).trans hc
  have ts := nafTblPt_mem K hL.n (a:=m+1) (by omega) (by omega)
  refine WP.mono (nafTablePoint_ok hL.lay hAcc hL.n hL.rxy hL.rxz ia.to_tmv hm ca
    (by have := hL.table_le; omega) ts (fun _ hx => List.mem_append_left _ hx) sep ja)
    fun t ⟨kt,it,jt⟩ => ?_
  refine ⟨(ka.mono (fun _ hx => List.mem_append_left _ hx)).trans
      (kt.mono (fun _ hx => List.mem_append_right _ hx)),?_,?_,jt⟩
  · exact it.sub (by intro x hx; simpa only [List.mem_append,or_assoc] using hx)
  · apply kt.invJ hL.lay hAcc ia.scr ts rs ?_ ja
    intro x hx hy
    have hs := hL.tbl x (List.mem_append_right _ (rr x hx))
    simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hy
    omega

end VG.Proof.Weierstrass.X86
