import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindow

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

structure JacWindowChecks (K : WinCfg) : Prop where
  tree : JacTreeChecks K
  treeCopy : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), dstOf i≠some r
  step : JacStepChecks K
  infinity : FieldCT (.block (Jacobian.infinity K K.R))
  counter : FieldCT (.block [.movz .x .x19 52 0])
  finish : FieldCT (Jacobian.jacFinish K)

theorem jacReset_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k e : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hOne : K.one<C.p) (hc : JacWindowChecks K) {P : Point C} :
    RelCT isa (fun s t => (∃ E,FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E s t) ∧
      JacCore K C base size P k e s ∧ JacCore K C base size P k e t)
      (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 52 0] : List Instr))) (JacPair K C base size P k 0 52) := by
  have raw : ∀ E, RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E)
      (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 52 0] : List Instr)))
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E' s t) := by
    intro E
    apply RelCT.block_append
    apply RelCT.seq (infinity_relCT hL.lay hAl (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [jacWinSlots,winOther]) hOne hc.infinity)
    have counter := fieldWP_relCT (M:=K.M) (size:=size) (base:=base) (Sl:=(·∈jacWinSlots K))
      (V:=[K.R.x,K.R.y,K.R.z]++jacLive K) (E:=infinityEnv K.M C.p K.one E K.R)
      hc.counter (fun s hi => WP.mono (setCounter_ok s (j:=52) (by decide)) fun _ ⟨_,hk⟩ =>
        ⟨hi.of_keeps hk (by decide),hk.sp⟩)
    exact counter.mono (fun _ _ h => h)
      (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _ hx)⟩)
  intro s t ts tt s' t' ⟨⟨E,pair⟩,cs,ct⟩ es et
  obtain ⟨he,pair'⟩ := raw E _ _ _ _ _ _ pair es et
  obtain ⟨_,_,xs,_,cs',ps⟩ := jacReset_ok hL hJ hAl hOne cs
  obtain ⟨_,_,xt,_,ct',pt⟩ := jacReset_ok hL hJ hAl hOne ct
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,pair',cs',ct',ps,pt⟩

def JacWindowInput (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (k : Nat) (s : State) : Prop :=
  wordsVal s.mem base K.zero K.M.n=0 ∧
  (∀ i<260,s.mem (off base (K.bits+i))=if k.testBit i then 1 else 0) ∧
  InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P

/-- Public points and scalar bits determine every window branch and table address. -/
theorem jacWindow_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1)
    (hk : 16*Window5.geom 52≤k) (hklt : k<32^52) (hc : JacWindowChecks K)
    {P : Point C} (hP : onCurve C P=true) {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E s t ∧
      JacWindowInput K C base P k s ∧ JacWindowInput K C base P k t)
      (Jacobian.jacWindow K 5) (fun s t => ∃ E',FieldPair K.M base size C.p
        (·∈combSlots (jacFinishCfg K).toComb) (jacFinishLive (jacFinishCfg K)) E' s t) := by
  have tree : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E s t ∧
      JacWindowInput K C base P k s ∧ JacWindowInput K C base P k t)
      (Jacobian.jacBuildTree K 16)
      (fun s t => (∃ E',FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E' s t) ∧
        JacCore K C base size P k 16 s ∧ JacCore K C base size P k 16 t) := by
    intro s t ts tt s' t' ⟨pair,⟨sz,sb,sp⟩,⟨tz,tb,tp⟩⟩ es et
    obtain ⟨he,pair'⟩ := jacTree_relCT hL hJ hAl hm hTbl hOne hc.tree hc.treeCopy _ _ _ _ _ _ pair es et
    obtain ⟨_,_,xs,ps⟩ := jacTree_ok hL hJ hAl hm hC ha hTbl hOne hP pair.left.to_tmv sp
    obtain ⟨_,_,xt,pt⟩ := jacTree_ok hL hJ hAl hm hC ha hTbl hOne hP pair.right.to_tmv tp
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    obtain ⟨is,ss⟩ := ps.ready hL sz sb
    obtain ⟨it,st⟩ := pt.ready hL tz tb
    exact ⟨he,pair',⟨is,ss,ps.point⟩,⟨it,st,pt.point⟩⟩
  change RelCT isa _ (.seq (Jacobian.jacBuildTree K 16)
    (.seq (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 52 0] : List Instr)))
      (.seq (.loop (Jacobian.jacStep K 5) (.nonzero .x .x19)) (Jacobian.jacFinish K)))) _
  apply RelCT.seq tree
  apply RelCT.seq (jacReset_relCT hL hJ hAl hOne hc)
  apply RelCT.seq (jacLoop_relCT hL hJ hAl hm hC ha hOne hTbl hBits hk hklt hc.step hP)
  intro s t ts tt s' t' ⟨⟨E',pair⟩,cs,_,_,_⟩ es et
  have hz : E' K.zero=0 := by
    rw [←pair.left.val _ (by simp [jacLive,winRo]),cs.stable.zero,toM_zero]
  have hpn := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [pair.left.mod.val] at hpn
  exact jacFinish_relCT hL hJ hAl hm hC hOne hone hBits hpn hc.finish hz _ _ _ _ _ _ pair es et

end VG.Proof.Weierstrass.AArch64
