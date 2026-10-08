import VerifiedGarbage.Proof.Weierstrass.X86.WinJacChoosePoint
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacAddLayout

/-! Branchless corrections for a zero accumulator or zero signed digit. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem repair_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk v j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) V E s)
    (hv : ∀ x∈jacCoords K.R++jacCoords K.D++jacCoords K.E,x∈V)
    (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s.mem (off base (K.bits+i))=if v.testBit i then 1 else 0) :
    WP isa (.block (nzMask 4 K.R.z++selPt 4 K.D K.E K.D++K.tc.digit++eqMask 0++selPt 4 K.R K.D K.R))
      s fun t => ∃ E', ProgKeep K.M base wk (jacCoords K.D++jacCoords K.R) s t ∧
      Inv K.M base size C.p (·∈slots K) (jacCoords K.R++(jacCoords K.D++V)) E' t ∧
      (E' K.R.x,E' K.R.y,E' K.R.z)=
        (if magH 16 (Window5.nib v j)=0 then (E K.R.x,E K.R.y,E K.R.z)
         else if E K.R.z=0 then (E K.E.x,E K.E.y,E K.E.z) else (E K.D.x,E K.D.y,E K.D.z)) := by
  have vr : ∀ x∈jacCoords K.R,x∈V := fun x hx => hv x (List.mem_append_left _ (List.mem_append_left _ hx))
  have vd : ∀ x∈jacCoords K.D,x∈V := fun x hx => hv x (List.mem_append_left _ (List.mem_append_right _ hx))
  have ve : ∀ x∈jacCoords K.E,x∈V := fun x hx => hv x (List.mem_append_right _ hx)
  have dw : ∀ x∈jacCoords K.D,x∈work K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [work]
  have rwk : ∀ x∈jacCoords K.R,x∈work K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [work]
  rw [List.append_assoc,List.append_assoc,List.append_assoc,WP.block_append_iff]
  have hmz := nz_field_ok (wk:=wk) hL.lay hm hi (vr K.R.z (by simp [jacCoords]))
  rw [hL.n] at hmz
  refine WP.mono hmz fun a ⟨ca,ia,ka⟩ => ?_
  rw [WP.block_append_iff,←hL.n]
  refine WP.mono (choose_point_ok hL.lay hW ia (point_nd hL (Or.inr (Or.inl rfl))) (points_apart hL).1
    (fun x hx => (List.mem_append.mp hx).elim (vd x) (ve x))
    (decide (E K.R.z≠0)) ca) fun b ⟨eb,kb,ib,ebd⟩ => ?_
  have kab : ProgKeep K.M base wk (jacCoords K.D) s b := (ka.mono (by simp)).trans kb
  have fb := (Frame.refl hi.scr hi.mod).field hL hW kab dw
  have bs : ∀ i<260,b.mem (off base (K.bits+i))=if v.testBit i then 1 else 0 := by
    intro i hi; rw [fb.bits hL hi]; exact hb i hi
  have hbs : K.bits+260≤size := by have := hL.bits; have := hL.table; omega
  have cb : b.gpr .esi=BitVec.ofNat 32 j := (kab.gpr _ (by decide)).trans hc
  have er (x : Nat) (hx : x∈jacCoords K.R) : eb x=E x :=
    value_after hL.lay hW hi ib kab (fun x hx => List.mem_append_right _ (dw x hx))
      (vr x hx) (List.mem_append_right _ (vr x hx)) (fun hd => (points_apart hL).2 x hx x hd rfl)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc ib.scr (k:=v) (N:=260) (by change 1≤5; decide) (by change 5<9; decide)
    (by change 5*j+5≤260; omega) hbs cb bs) fun c ⟨_,mc,kc⟩ => ?_
  have cm : c.gpr .ebx=BitVec.ofNat 32 (magH 16 (Window5.nib v j)) := by
    simpa only [JacWinCfg.tc,TCombCfg.H,Window5.combWin_five] using mc
  have mag : magH 16 (Window5.nib v j)≤16 := magH_le (Nat.mod_lt _ (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok c (by decide) (by omega) cm) fun d ⟨cd,kd,_⟩ => ?_
  have kcd : CKeeps clob b d := (kc.mono (by decide)).trans (kd.mono (by decide))
  have id := ib.of_keeps kcd (by decide)
  refine WP.mono (choose_point_ok hL.lay hW id (point_nd hL (Or.inl rfl)) (points_apart hL).2
    (fun x hx => (List.mem_append.mp hx).elim (fun hx => List.mem_append_right _ (vr x hx))
      (fun hx => List.mem_append_left _ hx)) (decide (magH 16 (Window5.nib v j)=0)) cd)
    fun t ⟨et,kt,it,etr⟩ => ?_
  have kk : ProgKeep K.M base wk (jacCoords K.D++jacCoords K.R) s t :=
    (kab.mono (fun _ hx => List.mem_append_left _ hx)).trans
      (((keep_of_ckeeps kcd).mono (by simp)).trans (kt.mono (fun _ hx => List.mem_append_right _ hx)))
  refine ⟨et,kk,it,?_⟩
  rw [etr,er _ (by simp [jacCoords]),er _ (by simp [jacCoords]),er _ (by simp [jacCoords]),ebd]
  by_cases hz : magH 16 (Window5.nib v j)=0
  · simp only [hz,decide_true,ite_true]
  · simp only [hz,decide_false,Bool.false_eq_true,ite_false]
    by_cases he : E K.R.z=0 <;> simp [he]

end VG.Proof.Weierstrass.X86.JWin
