import VerifiedGarbage.Proof.Weierstrass.X86.WinJacNeg
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacChoosePoint
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacAddMath
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacEntryState
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacFinish

/-! ## `WinJacFirst` -/

section

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

end

/-! ## `WinJacRepair` -/

section

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

end

/-! ## `WinJacAddStep` -/

section

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

end

/-! ## `WinJacStep` -/

section

/-! One full signed-window iteration. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem dec_counter_ok {s : State} {j : Nat} (hc : s.gpr .esi=BitVec.ofNat 32 (j+1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 j ∧ CKeeps [.esi] s t := by
  have he : BitVec.ofNat 32 (j+1)-(1 : BitVec 32)=BitVec.ofNat 32 j := by
    rw [BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  crun [hc,he]
  refine ⟨fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem test_counter_ok {s : State} {j : Nat} (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t =>
      t.zf=some (decide (j=0)) ∧ CKeeps [.esi] s t ∧ t.gpr .esi=BitVec.ofNat 32 j := by
  have he : (BitVec.ofNat 32 j==(0 : BitVec 32))=decide (j=0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this
      have hz : (0 : BitVec 32).toNat=0 := rfl
      omega
    · intro h; subst j; rfl
  crun [hc,BitVec.and_self,RegUpd.zf_arithFlags,he]
  exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩

theorem step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    {s₀ s : State} (h : Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J (j+1)) s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0) (hj : j<K.J)
    (hc : s.gpr .esi=BitVec.ofNat 32 (j+1))
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0) :
    WP isa K.step s fun t => Accum K C base size wk P k s₀ (Window5.winE (k+16*Window5.geom K.J) K.J j) t ∧
      t.gpr .esi=BitVec.ofNat 32 j ∧ t.zf=some (decide (j=0)) := by
  have hj52 : j<52 := by have := hL.J; omega
  unfold JacWinCfg.step
  apply WP.seq
  refine WP.mono (dec_counter_ok hc) fun a ⟨ca,ka⟩ => ?_
  apply WP.seq
  refine WP.mono (doubles_ok hL hW hm hC ha hP (h.keeps ka) hro hj52 ca) fun b ⟨ab,cb⟩ => ?_
  apply WP.seq
  refine WP.mono (read_fields_ok hL hW ab.frame ab.table hj52 cb hb) fun c ⟨pc,kc,cc⟩ => ?_
  have ac := ab.preserve hL hW kc (coords_work K) (fun x hx hy => entry_apart_R hL x hx (List.mem_append_left _ hy))
  apply WP.seq
  refine WP.mono (neg_fields_ok hL hW hm ac.frame pc hro hz hj52 cc hb) fun d ⟨pd,kd,cd⟩ => ?_
  have nw : ∀ x∈[K.neg,K.E.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  have nr : ∀ x∈[K.R.x,K.R.y,K.R.z],x∉[K.neg,K.E.y] := by
    intro x hx hy
    apply entry_apart_R hL x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl|rfl <;> simp [coords]
  have ad := ac.preserve hL hW kd nw nr
  have pd : Entry K C base (Window5.winPt C P (k+16*Window5.geom K.J) j) d := by
    have ep := Window5.winPt_mag P (k+16*Window5.geom K.J) j
    simpa only [ep,decide_eq_true_eq] using pd
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp (add_step_ok hL hW hm hC ha hO hP hP0 hn17 hn64 ad pd hro hj cd hb))
    fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono hu fun t ⟨acc_t,ct⟩ => ?_
  refine WP.mono (test_counter_ok hj52 ct) fun z ⟨fz,kz,cz⟩ => ⟨acc_t.keeps kz,cz,fz⟩

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacLoop` -/

section

/-! The complete constant-time signed-window multiplier. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem loop_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    {s₀ s : State} (h : Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J (K.J-1)) s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0) (hc : s.gpr .esi=BitVec.ofNat 32 (K.J-1))
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0) :
    WP isa (.loop K.step .ne) s (Accum K C base size wk P k s₀ k) := by
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j<K.J ∧ Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J j) t ∧ t.gpr .esi=BitVec.ofNat 32 j)
    (fun j u ⟨h1,hj,hu,cu⟩ => ?_) (K.J-1) s
    ⟨by have := hL.J; omega,by have := hL.J; omega,h,hc⟩
  have cu' : u.gpr .esi=BitVec.ofNat 32 (j-1+1) := by rw [show j-1+1=j by omega]; exact cu
  have hu' : Accum K C base size wk P k s₀ (Window5.winE (k+16*Window5.geom K.J) K.J (j-1+1)) u := by
    rw [show j-1+1=j by omega]; exact hu
  refine WP.mono (step_ok hL hW hm hC ha hO hP hP0 hn17 hn64 hu' hro hz (by omega) cu' hb)
    fun t ⟨ht,ct,ft⟩ => ?_
  by_cases he : j=1
  · subst j
    refine Or.inl ⟨?_,?_⟩
    · change Option.map Bool.not t.zf=some false
      rw [ft]; rfl
    · simpa only [Nat.sub_self,Window5.winE_zero,Nat.add_sub_cancel] using ht
  · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,ht,ct⟩
    change Option.map Bool.not t.zf=some true
    rw [ft,decide_eq_false (by omega)]
    rfl

theorem window_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    (hOne : K.one<C.p) (hOneM : toM C.p (2^(64*K.M.n)) K.one=1)
    {s : State} (hi : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P)
    (hz : tmv C K.M.n base s K.P.z=1) (h0 : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<260,s.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0)
    (hrec : k+16*Window5.geom K.J<32^K.J) :
    WP isa K.window s fun t => Frame K C base size wk s t ∧
      (∀ x∈jacCoords K.R,wordsVal t.mem base x K.M.n<C.p) ∧
      (k<C.n → Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul k P)) := by
  have zero : tmv C K.M.n base s K.zero=0 := by unfold tmv; rw [h0,toM_zero]
  unfold JacWinCfg.window
  apply WP.seq
  refine WP.mono (build_ok hL hW hm hC ha hO (by omega) hP hP0 hi hJ hz) fun a ba => ?_
  apply WP.seq
  refine WP.mono (first_ok (k:=k) hL hW hm hC hP ba.frame ba.table hi.lt zero hb (Nat.le_add_left _ _) hrec)
    fun b ⟨ab,cb⟩ => ?_
  apply WP.seq
  refine WP.mono (loop_ok hL hW hm hC ha hO hP hP0 hn17 hn64 ab hi.lt zero cb hb) fun c ac => ?_
  refine WP.mono (finish_ok hL hW hm hC hOne hOneM ac hi.lt h0) fun t ⟨kt,_,lt,rt⟩ =>
    ⟨ac.frame.field hL hW kt (fun _ hx => hx),lt,rt⟩

end VG.Proof.Weierstrass.X86.JWin

end
