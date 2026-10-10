import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeTiming

/-! ## `JacWindowFinish` -/

section

/-! Convert the final Jacobian result, reusing the comb's conversion proof. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def jacFinishCfg (K : WinCfg) : TCombCfg :=
  ⟨K.M,K.S,K.R,K.E,K.D,K.neg,K.zero,K.bits,260,"",5,52,(0,0),K.one⟩

/-- Conversion uses the same working slots as the fixed-base comb. -/
theorem jacFinishLayout {K : WinCfg} {size : Nat} (hL : JacWinLay K size) (hJ : K.J=52)
    (hBits : K.bits+5≤4096) : CombLay (jacFinishCfg K).toComb size := by
  have old := hL.toWinLay hJ
  have sub : ∀ x ∈ combSlots (jacFinishCfg K).toComb, x ∈ jacWinSlots K := by
    intro x hx; apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine { lay := { le := fun x hx => hL.lay.le x (sub x hx)
                    mo := fun x hx => hL.lay.mo x (sub x hx)
                    tmp := fun x hx => hL.lay.tmp x (sub x hx)
                    apart := fun x y hx hy hxy => hL.lay.apart x y (sub x hx) (sub y hy) hxy }
           add := old.rcbApart_D (Or.inr rfl)
           ro := ?_, nodup := hL.nodup, J := ?_, bits := ?_, bits4 := ?_, bits_w := ?_ }
  · intro x hx
    apply hL.ro x
    simp only [combRo,jacFinishCfg,TCombCfg.toComb,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winRo]
  · rw [TCombCfg.toComb_J]; change 1≤52 ∧ 52≤4096; decide
  · rw [TCombCfg.toComb_J]
    change K.bits+4*52≤size
    have := hL.bits; omega
  · change K.bits+3<4096; omega
  · intro w hw
    change w ∈ jacLoopWrites K at hw
    rw [TCombCfg.toComb_J]
    change K.bits+4*52≤w.1 ∨ w.1+w.2≤K.bits
    simp only [jacLoopWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨y,hy,rfl⟩ | rfl
    · have ht := hL.bits_w y (List.mem_append_left _ hy)
      dsimp only; rw [hL.n]; omega
    · have ht := hL.bits_tmp
      dsimp only; rw [hL.n]; omega

/-- A final canonical homogeneous representative, including infinity. -/
theorem jacFinish_ok {K : WinCfg} {C : Curve} {base : Addr} {size k e : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1) (hBits : K.bits+5≤4096)
    {P : Point C} {s : State} (h : JacCore K C base size P k e s) :
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
    simp only [rcbR,jacLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact jacComb_finish_ok lay al hC hm hL.n hOne hone pn h.field.scr h.field.mod hl h.stable.zero h.point

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JacWindow` -/

section

/-! The full public Jacobian variable-point multiplication. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Reset the accumulator and set the 52-digit public loop counter. -/
theorem jacReset_ok {K : WinCfg} {C : Curve} {base : Addr} {size k e : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hOne : K.one<C.p) {P : Point C} {s : State} (h : JacCore K C base size P k e s) :
    WP isa (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 52 0] : List Instr))) s fun t =>
      JacLoopKeep K base s t ∧ JacCore K C base size P k 0 t ∧ t.gpr .x19=52 := by
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
  have i' := ia.sub (fun x (hx : x ∈ jacLive K) => List.mem_append_right _ hx)
  have j' : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul 0 P) := by
    have he : mul 0 P=Point.infinity := by rw [Spec.Weierstrass.mul]; simp
    rw [he]; exact ja
  have ca := h.next hL hJ kp i' j'
  refine WP.mono (setCounter_ok a (j := 52) (by decide)) fun t ⟨t19,kt⟩ =>
    ⟨?_,ca.of_keeps kt (by decide),t19⟩
  refine ⟨((⟨kp.gpr,kp.rd,kp.wr,kp.sp⟩ : KeepRegs (clob K.M.n) s a).mono
    (fun _ hr => List.mem_cons_of_mem _ hr)).trans ((Keeps.regs kt).mono (by simp)),?_⟩
  simpa only [kt.mem,jacLoopWrites] using kp.unch

def jacWindowClob (K : WinCfg) : List Reg := .x20 :: tcombClob K.M.n

/-- Scalar multiplication with the signed five-bit table, 52 Jacobian
iterations, and one canonical homogeneous conversion. -/
theorem jacWindow_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1)
    (hk : 16*Window5.geom 52≤k) (hklt : k<32^52)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hz : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<260, s.mem (off base (K.bits+i))=if k.testBit i then 1 else 0)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Jacobian.jacWindow K 5) s fun t =>
      KeepRegs (jacWindowClob K) s t ∧ Unch base (jacTreeWrites K) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.R.x,K.R.y,K.R.z], wordsVal t.mem base x K.M.n<C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul (k-16*Window5.geom 52) P) := by
  change WP isa (.seq (Jacobian.jacBuildTree K 16)
    (.seq (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 52 0] : List Instr)))
      (.seq (.loop (Jacobian.jacStep K 5) (.nonzero .x .x19)) (Jacobian.jacFinish K)))) s _
  apply WP.seq
  refine WP.mono (jacTree_ok hL hJ hAl hm hC ha hTbl hOne hP hI hJP) fun a ta => ?_
  obtain ⟨ia,sa⟩ := ta.ready hL hz hb
  have ca : JacCore K C base size P k 16 a := ⟨ia,sa,ta.point⟩
  apply WP.seq
  refine WP.mono (jacReset_ok hL hJ hAl hOne ca) fun b ⟨kb,cb,b19⟩ => ?_
  apply WP.seq
  refine WP.mono (jacLoop_ok hL hJ hAl hm hC ha hOne hTbl hBits hk hklt hP cb b19)
    fun c ⟨kc,cc,_⟩ => ?_
  refine WP.mono (jacFinish_ok hL hJ hAl hm hC hOne hone hBits cc)
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

/-! ## `JacWindowFinishTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- The common final conversion drops the no-longer-used precomputation table. -/
theorem jacFinish_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1) (hBits : K.bits+5≤4096)
    (hpn : C.p<2^(64*K.M.n))
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
      (Jacobian.jacFinish K)) {E : Nat → Fe C} (hz : E K.zero=0) :
    RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E)
      (Jacobian.jacFinish K) (fun s t => ∃ E',FieldPair K.M base size C.p
        (·∈combSlots (jacFinishCfg K).toComb) (jacFinishLive (jacFinishCfg K)) E' s t) := by
  have lay := jacFinishLayout hL hJ hBits
  have al : CombA (jacFinishCfg K).toComb := ⟨fun x hx => hAl.sl x (by
    apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hAl.mod,fun _ _ h => nomatch (callOf_small (M := K.M) (Nat.le_of_eq hL.n)).symm.trans h⟩
  have sub : ∀ x∈jacFinishLive (jacFinishCfg K),x∈jacLive K := by
    intro x hx
    simp only [jacFinishLive,jacFinishCfg,TCombCfg.toComb,combRo,jacLive,winRo,
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

/-! ## `JacWindowTiming` -/

section

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

end
