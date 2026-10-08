import VerifiedGarbage.Proof.Weierstrass.X86.NafSigned

/-! A signed odd-multiple lookup preserves the running accumulator. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafLive_table (K : WinCfg) (hn : K.M.n=4) {a : Nat} (ha : 1≤a) (h8 : a≤8) :
    ∀ x∈jacCoords (K.tblPt a),x∈nafLive K := by
  intro x hx
  apply List.mem_append_right
  simp only [jacCoords,WinCfg.tblPt,hn,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by omega⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega),by omega⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega),by omega⟩

theorem NafCore.of_write {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
    {β : Nat → BitVec 8} {P : Point C} {s t : State} {W : List Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk)
    (h : NafCore K C base size P β e s) (hk : ProgKeep K.M base wk W s t)
    (hw : ∀ x∈W,x∈winOther K) (hn : ∀ x∈jacCoords K.R,x∉W)
    (hi : Inv K.M base size C.p (·∈nafSlots K) (nafLive K) (tmv C K.M.n base t) t) :
    NafCore K C base size P β e t :=
  ⟨hi,h.stable.keep hL hAcc hBitsWk h.field.scr (hk.mono hw),
    hk.invJ hL.lay hAcc h.field.scr (fun x hx => nafOther_slots K x (hw x hx))
      (fun x hx => h.field.sl x (nafLive_R K x hx)) hn h.point⟩

theorem nafEntry_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
    {β : Nat → BitVec 8} {b : BitVec 8} (hL : NafLay K size)
    (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hmag : 1≤nafMagnitude b) (hmag15 : nafMagnitude b≤15) (hodd : nafMagnitude b%2=1)
    {P : Point C} {s : State} (h : NafCore K C base size P β e s)
    (h8 : s.gpr .ebx=b.setWidth 32) :
    WP isa (Naf.signedEntry K F) s fun t =>
      ProgKeep K.M base wk (winOther K) s t ∧ NafCore K C base size P β e t ∧
      Inv K.M base size C.p (·∈nafSlots K) (jacCoords K.E++nafLive K) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.E.z)
        (if nafNegative b then negPt (mul (nafMagnitude b) P) else mul (nafMagnitude b) P) := by
  let a := (nafMagnitude b-1)/2+1
  have ha : 1≤a := by dsimp [a]; omega
  have ha8 : a≤8 := by dsimp [a]; omega
  have he : 2*a-1=nafMagnitude b := by dsimp [a]; omega
  have hw : ∀ x∈jacCoords K.E,x∈winOther K := by
    intro x hx
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hd : ∀ x∈jacCoords K.E,x∈nafSlots K := fun x hx => nafOther_slots K x (hw x hx)
  have hn := hL.nodup
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hn
  have hr : ∀ x∈jacCoords K.R,x∉jacCoords K.E := by
    intro x hx hy
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx hy
    grind
  have h0 : K.zero∈nafLive K := by
    simp [nafLive,nafTableLive,winRo]
  have hz : tmv C K.M.n base s K.zero=0 := by unfold tmv; rw [h.stable.zero,toM_zero]
  have h0E : K.zero∉jacCoords K.E := fun he => hL.ro _ (by simp [winRo]) (hw _ he)
  have sep : K.E.x+96≤K.tbl ∨ K.tbl+768≤K.E.x := by
    have hx := hL.tbl K.E.x (List.mem_append_right _ (hw _ (by simp [jacCoords])))
    have hz := hL.tbl K.E.z (List.mem_append_right _ (hw _ (by simp [jacCoords])))
    rw [hL.exz] at hz
    omega
  refine WP.mono (nafSignedEntry_of_lookup hL.lay hAcc hm hL.exy hL.exz h.field h0 hz h0E h8
    (P := mul (nafMagnitude b) P) (fun u iu hu => ?_)) fun t ⟨kt,it,jt⟩ => ?_
  · have jp := h.stable.table a ha ha8
    rw [he] at jp
    exact nafPublicPoint_ok hL.lay hAcc hL.n hL.exy hL.exz iu hu hmag hmag15
      (by have := hL.table_le; omega) hd (nafLive_table K hL.n ha ha8) sep jp
  · refine ⟨kt.mono hw,h.of_write hL hAcc hBitsWk kt hw hr
      (it.sub (fun _ hx => List.mem_append_right _ hx)),it,?_⟩
    by_cases hb : b.toNat<128
    · simpa only [nafNegative,show ¬128≤b.toNat from by omega,decide_false,Bool.false_eq_true,ite_true,ite_false,hb] using jt
    · simpa only [nafNegative,show 128≤b.toNat from by omega,decide_true,ite_false,ite_true,hb] using jt

end VG.Proof.Weierstrass.X86
