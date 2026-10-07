import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindow

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

structure NafWindowChecks (K : WinCfg) : Prop where
  tree : NafTableChecks K
  treeCopy : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), dstOf i≠some r
  step : NafStepChecks K
  infinity : FieldCT (.block (Jacobian.infinity K K.R))
  counter : FieldCT (.block [.movz .x .x19 256 0])
  finish : FieldCT (Jacobian.jacFinish K)

theorem nafReset_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k e : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hOne : K.one<C.p) (hc : NafWindowChecks K) {P : Point C} :
    RelCT isa (fun s t => (∃ E,FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t) ∧
      NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t)
      (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 256 0] : List Instr))) (NafPair K C base size P k 0 256) := by
  have raw : ∀ E, RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E)
      (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 256 0] : List Instr)))
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E' s t) := by
    intro E
    apply RelCT.block_append
    apply RelCT.seq (infinity_relCT hL.lay hAl (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [jacWinSlots,winOther]) hOne hc.infinity)
    have counter := fieldWP_relCT (M:=K.M) (size:=size) (base:=base) (Sl:=(·∈jacWinSlots K))
      (V:=[K.R.x,K.R.y,K.R.z]++nafLive K) (E:=infinityEnv K.M C.p K.one E K.R)
      hc.counter (fun s hi => WP.mono (setCounter_ok s (j:=256) (by decide)) fun _ ⟨_,hk⟩ =>
        ⟨hi.of_keeps hk (by decide),hk.sp⟩)
    exact counter.mono (fun _ _ h => h)
      (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _ hx)⟩)
  intro s t ts tt s' t' ⟨⟨E,pair⟩,cs,ct⟩ es et
  obtain ⟨he,pair'⟩ := raw E _ _ _ _ _ _ pair es et
  obtain ⟨_,_,xs,_,cs',ps⟩ := nafReset_ok hL hJ hAl hOne cs
  obtain ⟨_,_,xt,_,ct',pt⟩ := nafReset_ok hL hJ hAl hOne ct
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,pair',cs',ct',ps,pt⟩

def NafWindowInput (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (k : Nat) (s : State) : Prop :=
  wordsVal s.mem base K.zero K.M.n=0 ∧
  (∀ i<257,s.mem (off base (K.bits+i))=Naf5.byte k i) ∧
  InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P

/-- Public points and scalar bits determine every window branch and table address. -/
theorem nafWindow_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1)
    (hk : k<2^256) (hc : NafWindowChecks K)
    {P : Point C} (hP : onCurve C P=true) {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E s t ∧
      NafWindowInput K C base P k s ∧ NafWindowInput K C base P k t)
      (Naf.window K) (fun s t => ∃ E',FieldPair K.M base size C.p
        (·∈combSlots (jacFinishCfg K).toComb) (jacFinishLive (jacFinishCfg K)) E' s t) := by
  have tree : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E s t ∧
      NafWindowInput K C base P k s ∧ NafWindowInput K C base P k t)
      (Naf.table K)
      (fun s t => (∃ E',FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E' s t) ∧
        NafCore K C base size P (Naf5.byte k) 15 s ∧ NafCore K C base size P (Naf5.byte k) 15 t) := by
    intro s t ts tt s' t' ⟨pair,⟨sz,sb,sp⟩,⟨tz,tb,tp⟩⟩ es et
    obtain ⟨he,pair'⟩ := nafTable_relCT hL hJ hAl hm hTbl hOne hc.tree hc.treeCopy _ _ _ _ _ _ pair es et
    obtain ⟨_,_,xs,ps⟩ := nafTable_ok hL hJ hAl hm hC ha hTbl hOne hP pair.left.to_tmv sp
    obtain ⟨_,_,xt,pt⟩ := nafTable_ok hL hJ hAl hm hC ha hTbl hOne hP pair.right.to_tmv tp
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    obtain ⟨is,ss⟩ := ps.ready hL sz sb
    obtain ⟨it,st⟩ := pt.ready hL tz tb
    exact ⟨he,pair',⟨is,ss,ps.point⟩,⟨it,st,pt.point⟩⟩
  rw [Naf.window]
  apply RelCT.seq tree
  apply RelCT.seq (nafReset_relCT hL hJ hAl hOne hc)
  apply RelCT.assoc
  apply RelCT.seq (nafRun_relCT hL hJ hAl hm hC ha hOne hTbl (by omega) hk hc.step hP)
  intro s t ts tt s' t' ⟨⟨E',pair⟩,cs,_,_,_⟩ es et
  have hz : E' K.zero=0 := by
    rw [←pair.left.val _ (by simp [nafLive,winRo]),cs.stable.zero,toM_zero]
  have hpn := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [pair.left.mod.val] at hpn
  exact nafFinish_relCT hL hJ hAl hm hC hOne hone hBits hpn hc.finish hz _ _ _ _ _ _ pair es et

end VG.Proof.Weierstrass.AArch64
