import VerifiedGarbage.Proof.Weierstrass.X86.NafLoopTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafFinish

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure NafWindowChecks (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prop where
  table : NafTableChecks K F
  step : NafStepChecks K F
  infinity : ScratchCT (.block (Jacobian.infinity K K.R))
  initCounter : RegCT [.esi] (.block [.mov .esi (.imm 256)])
  finish : ScratchCT (Naf.finish K F)

theorem nafWindow_init_fields_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} {E : Nat → Fe C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p) (hc : NafWindowChecks K F) :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E counter)
      (.seq (Naf.table K F) (.block (Jacobian.infinity K K.R ++ ([.mov .esi (.imm 256)] : List Instr))))
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E' 256 s t) := by
  apply RelCT.seq (nafTable_relCT hL hW hJ hm hOne hc.table)
  apply RelCT.exists_
  intro E'
  apply RelCT.block_append
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := by
    intro x hx
    apply nafOther_slots K
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  apply RelCT.seq (infinity_relCT hL.lay hW rs hOne hc.infinity)
  have init := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p) (Sl:=(·∈nafSlots K))
    (V:=jacCoords K.R++nafLive K) (E:=infinityEnv K.M C.p K.one E' K.R) (counter:=8) (counter':=256)
    (Pre:=fun _ => True) (Post:=fun _ => True) (ws:=[.esi]) (by decide) hc.initCounter
    (fun _ _ hp _ _ => hp.pub.agree (by
      intro r hr; rw [List.mem_singleton.mp hr]; exact hp.count₁.trans hp.count₂.symm))
    (fun s _ _ _ => WP.mono (nafRun_initCounter_ok s) (fun _ ⟨ct,hk⟩ => ⟨ct,trivial,hk⟩))
  exact init.mono (fun _ _ h => ⟨h,trivial,trivial⟩)
    (fun _ _ h => ⟨_,h.1.sub (fun _ hx => List.mem_append_right _ hx)⟩)

theorem nafWindow_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} {E : Nat → Fe C} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hk : k<2^256) (hP : onCurve C P=true)
    (hc : NafWindowChecks K F) :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E counter s t ∧
      NafInput K C base P k s ∧ NafInput K C base P k t)
      (Naf.window K F) (NafRunPair K C base size P (Naf5.byte k) k 0) := by
  have raw := (nafWindow_init_fields_relCT (base:=base) (E:=E) (counter:=counter) hL hJ hW hm hOne hc).mono
    (P':=fun (s t : State) => FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E counter s t ∧
      NafInput K C base P k s ∧ NafInput K C base P k t)
    (fun _ _ h => h.1) (fun _ _ h => h)
  have init := raw.wp (fun _ _ ⟨h,ps,pt⟩ =>
    ⟨WP.mono (nafWindow_init_ok hL hJ hW hBitsWk hm hC ha hOne hP h.left.to_tmv ps.point ps.zero ps.bits)
        (fun _ h => h.2.2.1),
     WP.mono (nafWindow_init_ok hL hJ hW hBitsWk hm hC ha hOne hP h.right.to_tmv pt.point pt.zero pt.bits)
        (fun _ h => h.2.2.1)⟩)
  unfold Naf.window
  apply RelCT.assoc
  exact init.seq (nafRun_relCT hL hJ hW hBitsWk hm hC ha hOne hk hP hc.step)

end VG.Proof.Weierstrass.X86
