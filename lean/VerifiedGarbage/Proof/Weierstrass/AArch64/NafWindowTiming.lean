import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming

/-! ## `NafFinish` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- A final canonical homogeneous representative, including infinity. -/
theorem nafFinish_ok {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat} {β : Nat → BitVec 8}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1) (hBits : K.bits+5≤4096)
    {P : Point C} {s : State} (h : NafCore K C base size P β e s) :
    WP isa (Jacobian.jacFinish K) s fun t =>
      KeepRegs (tcombClob K.M.n) s t ∧ Unch base (jacLoopWrites K) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.R.x,K.R.y,K.R.z], wordsVal t.mem base x K.M.n<C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul e P) := by
  have lay := jacFinishLayout hL hJ hBits
  have al : CombA (jacFinishCfg K).toComb := ⟨fun x hx => hAl.sl x (by
    apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hAl.mod,fun _ _ h => nomatch (callOf_small (M := K.M) (Nat.le_of_eq hL.n)).symm.trans h⟩
  have pn := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [h.field.mod.val] at pn
  have hl : ∀ x ∈ rcbR K.S K.R ⟨K.zero,K.zero,K.zero⟩, wordsVal s.mem base x K.M.n<C.p := by
    intro x hx
    apply h.field.lt x
    simp only [rcbR,nafLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact jacComb_finish_ok lay al hC hm hL.n hOne hone pn h.field.scr h.field.mod hl h.stable.zero h.point

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafFinishTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- The common final conversion drops the no-longer-used precomputation table. -/
theorem nafFinish_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1) (hBits : K.bits+5≤4096)
    (hpn : C.p<2^(64*K.M.n))
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
      (Jacobian.jacFinish K)) {E : Nat → Fe C} (hz : E K.zero=0) :
    RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E)
      (Jacobian.jacFinish K) (fun s t => ∃ E',FieldPair K.M base size C.p
        (·∈combSlots (jacFinishCfg K).toComb) (jacFinishLive (jacFinishCfg K)) E' s t) := by
  have lay := jacFinishLayout hL hJ hBits
  have al : CombA (jacFinishCfg K).toComb := ⟨fun x hx => hAl.sl x (by
    apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hAl.mod,fun _ _ h => nomatch (callOf_small (M := K.M) (Nat.le_of_eq hL.n)).symm.trans h⟩
  have sub : ∀ x∈jacFinishLive (jacFinishCfg K),x∈nafLive K := by
    intro x hx
    simp only [jacFinishLive,jacFinishCfg,TCombCfg.toComb,combRo,nafLive,winRo,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have sl : ∀ x∈jacFinishLive (jacFinishCfg K),x∈combSlots (jacFinishCfg K).toComb := by
    intro x hx
    simp only [jacFinishLive,combSlots,combRo,jacFinishCfg,TCombCfg.toComb,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact (jacCombFinish_relCT lay al hC hm hL.n hOne hone hpn hct hz).mono
    (fun _ _ p => ⟨⟨p.left.scr,p.left.mod,sl,fun x hx => p.left.lt x (sub x hx),
      fun x hx => p.left.val x (sub x hx)⟩,
      ⟨p.right.scr,p.right.mod,sl,fun x hx => p.right.lt x (sub x hx),
      fun x hx => p.right.val x (sub x hx)⟩,p.sp⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafWindow` -/

section

/-! The full public Jacobian variable-point multiplication. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Reset the accumulator and set the 256-iteration public loop counter. -/
theorem nafReset_ok {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat} {β : Nat → BitVec 8}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hOne : K.one<C.p) {P : Point C} {s : State} (h : NafCore K C base size P β e s) :
    WP isa (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 256 0] : List Instr))) s fun t =>
      JacLoopKeep K base s t ∧ NafCore K C base size P β 0 t ∧ t.gpr .x19=256 := by
  rw [WP.block_append_iff]
  have sl : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ jacWinSlots K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [jacWinSlots,winOther]
  refine WP.mono (infinityPoint_ok hL.lay hAl sl h.field hOne) fun a ⟨E,ka,ia,ja⟩ => ?_
  have kp : ProgKeep K.M base (winOther K) s a := ka.mono (by
    intro x hx
    simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind)
  have i' := ia.sub (fun x (hx : x ∈ nafLive K) => List.mem_append_right _ hx)
  have j' : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul 0 P) := by
    have he : mul 0 P=Point.infinity := by rw [Spec.Weierstrass.mul]; simp
    rw [he]; exact ja
  have ca := h.next hL hJ kp i' j'
  refine WP.mono (setCounter_ok a (j := 256) (by decide)) fun t ⟨t19,kt⟩ =>
    ⟨?_,ca.of_keeps kt (by decide),t19⟩
  refine ⟨((⟨kp.gpr,kp.rd,kp.wr,kp.sp⟩ : KeepRegs (clob K.M.n) s a).mono
    (fun _ hr => List.mem_cons_of_mem _ hr)).trans ((Keeps.regs kt).mono (by simp)),?_⟩
  simpa only [kt.mem,jacLoopWrites] using kp.unch



/-- Scalar multiplication with the sparse signed five-bit table, 256 Jacobian
iterations, and one canonical homogeneous conversion. -/
theorem nafWindow_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1)
    (hk : k<2^256)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hz : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<257, s.mem (off base (K.bits+i))=Naf5.byte k i)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Naf.window K) s fun t =>
      KeepRegs (jacWindowClob K) s t ∧ Unch base (jacTreeWrites K) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.R.x,K.R.y,K.R.z], wordsVal t.mem base x K.M.n<C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul k P) := by
  rw [Naf.window]
  apply WP.seq
  refine WP.mono (nafTable_ok hL hJ hAl hm hC ha hTbl hOne hP hI hJP) fun a ta => ?_
  obtain ⟨ia,sa⟩ := ta.ready hL hz hb
  have ca : NafCore K C base size P (Naf5.byte k) 15 a := ⟨ia,sa,ta.point⟩
  apply WP.seq
  refine WP.mono (nafReset_ok hL hJ hAl hOne ca) fun b ⟨kb,cb,b19⟩ => ?_
  apply WP.assoc
  apply WP.seq
  refine WP.mono (nafRun_ok hL hJ hAl hm hC ha hOne hTbl (by omega) hk hP cb b19)
    fun c ⟨kc,cc,_⟩ => ?_
  refine WP.mono (nafFinish_ok hL hJ hAl hm hC hOne hone hBits cc)
    fun t ⟨kt,ut,mt,lt,pt⟩ => ⟨?_,?_,mt,lt,pt⟩
  · have tr : ∀ r ∈ jacTreeClob K, r ∈ jacWindowClob K := by
      rw [jacTreeClob,jacWindowClob,hL.n]; decide
    have lr : ∀ r ∈ Reg.x19::clob K.M.n, r ∈ jacWindowClob K := by
      rw [jacWindowClob,hL.n]; decide
    exact (ta.keep.mono tr).trans ((kb.regs.mono lr).trans
      ((kc.regs.mono lr).trans (kt.mono (fun _ hr => List.mem_cons_of_mem _ hr))))
  · have sub : ∀ w ∈ jacLoopWrites K, w ∈ jacTreeWrites K := by
      intro w hw
      simp only [jacLoopWrites,jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
      rcases hw with ⟨x,hx,rfl⟩ | rfl
      · exact Or.inl ⟨x,List.mem_append_left _ hx,rfl⟩
      · exact Or.inr rfl
    have u1 := ta.unch.trans (kb.mem.mono sub)
    have u2 := (kc.mem.mono sub).trans (ut.mono sub)
    exact (u1.trans u2).mono (fun _ hw => by
      simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | (hw | hw) <;> exact hw)

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafWindowTiming` -/

section

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

end
