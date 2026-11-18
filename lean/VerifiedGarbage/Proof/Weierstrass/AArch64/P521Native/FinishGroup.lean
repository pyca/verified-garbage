module

public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.WindowJA
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeLayout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProjectiveState
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishCounter
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProjective
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFixY
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAddCode
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeInverse
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishOutput
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.LookupCode
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowDoublePair

/-! ### `Weierstrass.AArch64.P521Native.WindowFiveDoubles`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

structure WindowLoopStable (s t : State) : Prop where
  base : t.gpr .x0=s.gpr .x0
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  gp : ∀r∈preserved,r≠.x30 → r≠.x19 → t.gpr r=s.gpr r
  v29 : t.v .v29=s.v .v29
  v31 : t.v .v31=s.v .v31

 theorem WindowLoopStable.trans {s t u : State} (h : WindowLoopStable s t) (k : WindowLoopStable t u) : WindowLoopStable s u :=
  ⟨k.base.trans h.base,k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp,
    fun r hr hn hc => (k.gp r hr hn hc).trans (h.gp r hr hn hc),k.v29.trans h.v29,k.v31.trans h.v31⟩

 theorem WindowLoopStable.scr {s t : State} {W : Nat} (h : WindowLoopStable s t) (hs : Scr s (s.gpr .x0) W) :
    Scr t (t.gpr .x0) W := by
  refine ⟨rfl,?_,?_,hs.enc⟩
  · rw [h.base,h.wr]; exact hs.wr
  · rw [h.base]; exact hs.nowrap

def windowDoubleBody : Prog isa := .seq windowDoublePair (.block outerBlock140)

 theorem window_double_body_ok {s : State} {W j c : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (hj : j<4294967296) (hc : 1≤c) (hc2 : c≤2) (counter : s.gpr .x19=windowPacked j c) :
    WP isa windowDoubleBody s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧
      t.gpr .x19=windowPacked j (c-1) ∧ t.gpr .x2=BitVec.ofNat 64 (c-1) := by
  rw [windowDoubleBody,WP.seq_iff]
  refine WP.mono (window_double_pair_ok hs room bound) fun u ⟨b,p,frame,ku⟩ => ?_
  refine WP.mono (window_counter_pair u) fun t ⟨e19,e2,kt,vt⟩ => ?_
  have uc : u.gpr .x19=windowPacked j c := (ku.gp .x19 (by decide) (by decide)).trans counter
  rw [uc,window_counter_pair_value j c hc] at e19 e2
  rw [window_counter_high j (c-1) hj (by omega_arith)] at e2
  have fresh : ∀r∈preserved,r≠.x19 → r∉[Reg.x19,Reg.x2] := by decide
  refine ⟨?_,?_,?_,?_,e19,e2⟩
  · rw [kt.mem]; exact b
  · rw [kt.mem]; exact p
  · rw [kt.mem]; exact frame
  · exact ⟨(kt.gpr _ (by decide)).trans ku.base,kt.rd.trans ku.rd,kt.wr.trans ku.wr,kt.sp.trans ku.sp,
      fun r hr hn h19 => (kt.gpr r (fresh r hr h19)).trans (ku.gp r hr hn),
      by rw [vt,ku.v29],by rw [vt,ku.v31]⟩

 theorem window_double_body_source {s : State} {Q : State → Prop} :
    WP isa windowDoubleBody s Q ↔ WP isa (sequence [
      .block outerBlock138,callNormalDouble,.block outerBlock139,callNormalDouble,.block outerBlock140]) s Q := by
  simp only [windowDoubleBody,windowDoublePair,sequence,List.foldr_cons,List.foldr_nil,VG.WP.seq_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 theorem window_double_loop_one {s : State} {W j : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (hj : j<4294967296) (counter : s.gpr .x19=windowPacked j 1) :
    WP isa loop24 s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x2=0#64 := by
  have body := (window_double_body_source).mp
    (window_double_body_ok hs room bound hj (by decide : 1≤1) (by decide) counter)
  obtain ⟨trace,t,exec,b,p,frame,k,e19,e2⟩ := body
  have cond : isa.eval (.nonzero .x .x2) t=some false := by
    change some (t.gpr .x2 != 0)=some false
    rw [e2]; rfl
  refine ⟨_,t,Exec.loopExit exec cond,b,p,frame,k,?_,e2⟩
  · simpa only [Nat.sub_self,windowPacked,Nat.zero_mul,Nat.add_zero] using e19

 theorem window_double_loop_two {s : State} {W j : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (hj : j<4294967296) (counter : s.gpr .x19=windowPacked j 2) :
    WP isa loop24 s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=
        windowDbl (windowDbl (windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072)))) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x2=0#64 := by
  have body := (window_double_body_source).mp
    (window_double_body_ok hs room bound hj (by decide : 1≤2) (by decide) counter)
  obtain ⟨trace,u,exec,b,p,frame,k,e19,e2⟩ := body
  have cond : isa.eval (.nonzero .x .x2) u=some true := by
    change some (u.gpr .x2 != 0)=some true
    rw [e2]; rfl
  have hu := k.scr hs
  have bu : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [k.base]; exact b
  obtain ⟨trace',t,exec',bt,pt,ft,kt,t19,t2⟩ := window_double_loop_one hu room bu hj e19
  rw [k.base] at bt pt ft
  refine ⟨_,t,Exec.loopNext exec cond exec',bt,?_,WindowWorkFrame.trans frame ft,k.trans kt,t19,t2⟩
  rw [pt,p]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 def windowFiveDoubles : Prog isa := .seq loop24 (.seq (.block outerBlock141) callNormalDouble)

 theorem window_five_doubles_ok {s : State} {W j : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (hj : j<4294967296) (counter : s.gpr .x19=windowPacked j 2) :
    WP isa windowFiveDoubles s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1288=
        windowDbl (windowDbl (windowDbl (windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072))))) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧
      t.gpr .x19=BitVec.ofNat 64 j := by
  rw [windowFiveDoubles,WP.seq_iff]
  refine WP.mono (window_double_loop_two hs room bound hj counter) fun u ⟨bu,pu,fu,ku,counterU,_⟩ => ?_
  have hu := ku.scr hs
  have hb : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [ku.base]; exact bu
  refine WP.mono (window_double_step_ok hu room double_layout_forward hb (window_args_extra u))
    fun t ⟨bt,pt,ft,kt⟩ => ?_
  rw [ku.base] at bt pt ft
  refine ⟨bt,?_,WindowWorkFrame.trans fu (DoubleFrame.window ft (by decide) (by decide)),?_,?_⟩
  · change ordinaryPoint t.mem (s.gpr .x0) 1288=windowDbl (ordinaryPoint u.mem (s.gpr .x0) 1072) at pt
    rw [pt,pu]
  · exact ⟨kt.base.trans ku.base,kt.rd.trans ku.rd,kt.wr.trans ku.wr,kt.sp.trans ku.sp,
      fun r hr hn h19 => (kt.gp r hr hn).trans (ku.gp r hr hn h19),
      kt.v29.trans ku.v29,kt.v31.trans ku.v31⟩
  · exact (kt.gp .x19 (by decide) (by decide)).trans counterU

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! ### `Weierstrass.AArch64.P521Native.FinishFrontReady`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.AArch64.P521Native.FinishAssemble`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.AArch64.P521Native.FinishLookup`, which this module and modules that import it used -/

section

/-! The final digit reuses the exact main-loop constant-time affine lookup. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

def finishLookupCode : List Instr := (outerBlock152.drop 209).take 693

theorem finish_lookup_source : finishLookupCode=(outerBlock142.drop 54).take 693 := by lit_decide

theorem finish_vector_lookup_source : (outerBlock152.drop 231).take 564=lookupCode := by lit_decide

/-- Any machine contract for the full main-loop nibble/lookup/sign-selection
phase applies to the final digit unchanged; its public index is zero. -/
theorem finish_lookup_wp {s : State} {Q : State → Prop}
    (h : WP isa (.block ((outerBlock142.drop 54).take 693)) s Q) :
    WP isa (.block finishLookupCode) s Q := by
  rw [finish_lookup_source]
  exact h

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! ### `Weierstrass.AArch64.P521Native.FinishChecks`, which this module and modules that import it used -/

section

/-! Original ECDH security checks and masked serialization, independently of
how the affine shared coordinate was obtained. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ecdh.AArch64

 theorem checked_finish_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64}
    (mn : wordsVal s.mem base (c.sl MN) c.n=c.C.n) (saved : Spill.Saved base g Cfg.saved s.mem)
    {V : Prop} [Decidable V] (hflag : word s.mem base (c.sl FLAG)=mask V) {out : Addr}
    (hx20 : s.gpr .x20=out) (hfit : out.toNat+c.C.len≤2^64)
    (hw : (⟨out,c.C.len⟩ : Region)∈s.wr) (hd : Region.Disjoint ⟨out,c.C.len⟩ ⟨base,size⟩) :
    WP isa (.block (c.checkRange (c.sl D)++c.checkNonzero (c.sl RZ)++VG.Impl.Ecdh.AArch64.Cfg.finish c)) s fun t =>
      VG.Spec.Ecdsa.bytesAt t.mem out c.C.len=
        (if ok c base s V then VG.Spec.Weierstrass.toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0) ∧
      (t.gpr .x0).setWidth 32=(if ok c base s V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hf : c.sl FLAG+8≤size := by have := sl_le c h7 (i:=FLAG) (by decide); omega_arith
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (checkRange_ok c hs h0 (sl_le c h7 (i:=D) (by decide)) (sl_le c h7 (i:=MN) (by decide))
    hf (sl_mod8 c D) (sl_mod8 c MN) (sl_mod8 c FLAG)) fun u ⟨fu,ku,Ou⟩ => ?_
  have hsu := hs.of_keepRegs ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hsu h0 (sl_le c h7 (i:=RZ) (by decide)) hf
    (sl_mod8 c RZ) (sl_mod8 c FLAG)) fun v ⟨fv,kv,Ov⟩ => ?_
  have hsv := hsu.of_keepRegs kv (by decide)
  have lowFlag : ∀w∈[(c.sl FLAG,8)],64≤w.1 := by
    intro w hw
    obtain rfl := List.mem_singleton.mp hw
    exact sl_ge64 c FLAG
  have savedV := Saved.unch (Saved.unch saved lowFlag Ou.unch) lowFlag Ov.unch
  have flagv : word v.mem base (c.sl FLAG)=if ok c base s V then BitVec.allOnes 64 else 0 := by
    rw [fv,fu,hflag,sv_flag Ou h0 h7 hn (i:=RZ) (by decide) (by decide),mn,mask_and,mask_and]
    simp only [mask,decide_eq_true_eq,and_assoc]
  have outv : v.gpr .x20=out := by rw [kv.gpr _ (by decide),ku.gpr _ (by decide),hx20]
  have wrv : (⟨out,c.C.len⟩ : Region)∈v.wr := by rw [kv.wr,ku.wr]; exact hw
  refine WP.mono (ecFinish_ok hc hsv outv hfit wrv hd savedV _ flagv) fun t ⟨bytes,ret,saved⟩ => ⟨?_,ret,saved⟩
  have xv : sv c base v X=sv c base s X :=
    (sv_flag Ov h0 h7 hn (i:=X) (by decide) (by decide)).trans
      (sv_flag Ou h0 h7 hn (i:=X) (by decide) (by decide))
  rw [bytes,xv]

/-- The exact emitted final block retains scalar/nonzero validation and the
original output/ABI contract, including every invalid-input path. -/
theorem native_finish_output_ok (hc : BaseCfgOk VG.Impl.Weierstrass.AArch64.P521Native.config)
    {base : Addr} {s : State} (hs : Scr s base size) {g : Reg → BitVec 64}
    (mn : wordsVal s.mem base 136 9=VG.Impl.Weierstrass.AArch64.P521Native.config.C.n)
    (saved : Spill.Saved base g Cfg.saved s.mem)
    {V : Prop} [Decidable V]
    (hflag : word s.mem base 3232=mask V) {out : Addr}
    (hx20 : s.gpr .x20=out) (hfit : out.toNat+66≤2^64)
    (hw : (⟨out,66⟩ : Region)∈s.wr) (hd : Region.Disjoint ⟨out,66⟩ ⟨base,size⟩) :
    WP isa (.block VG.Impl.Weierstrass.AArch64.P521Native.outerBlock171) s fun t =>
      VG.Spec.Ecdsa.bytesAt t.mem out 66=
        (if ok VG.Impl.Weierstrass.AArch64.P521Native.config base s V then
          VG.Spec.Weierstrass.toBytes 66 (wordsVal s.mem base 2584 9) else List.replicate 66 0) ∧
      (t.gpr .x0).setWidth 32=(if ok VG.Impl.Weierstrass.AArch64.P521Native.config base s V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) := by
  apply finish_output_wp
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.AArch64.Mont.lr_ok s) fun u ⟨_,ku⟩ => ?_)
  have hsu := hs.of_keeps ku (by decide)
  have mnu : wordsVal u.mem base 136 9=VG.Impl.Weierstrass.AArch64.P521Native.config.C.n := by
    rw [ku.mem]; exact mn
  have savedU : Spill.Saved base g Cfg.saved u.mem := ku.mem.symm ▸ saved
  have flagu : word u.mem base 3232=mask V := by rw [ku.mem]; exact hflag
  have outu : u.gpr .x20=out := (ku.gpr .x20 (by decide)).trans hx20
  have wru : (⟨out,66⟩ : Region)∈u.wr := by rw [ku.wr]; exact hw
  refine WP.mono (checked_finish_ok hc hsu mnu savedU flagu outu hfit wru hd) fun t ht => ?_
  simpa only [ok,sv,ku.mem,
    (show VG.Impl.Weierstrass.AArch64.P521Native.config.C.len=66 from rfl),
    (show VG.Impl.Weierstrass.AArch64.P521Native.config.n=9 from rfl),
    (show VG.Impl.Weierstrass.AArch64.P521Native.config.sl X=2584 from rfl)] using ht

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! ### `Weierstrass.AArch64.P521Native.FinishProducts`, which this module and modules that import it used -/

section

/-! Final ordinary-field products retain all calls of the selected prototype. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native
open VG.Proof.Mont.AArch64.P521Field

def finishProductsOps : List PointOp := [.mul 2512 1072 2152 false,.mul 2584 2512 352 false]

theorem finish_products_source169 : outerBlock169=normalizeCallArgs 2512 1072 2152 := by lit_decide

theorem finish_products_source170 : outerBlock170=buildRestore++normalizeCallArgs 2584 2512 352 := by lit_decide

def finishProductsMachine : Prog isa := sequence [
  .block outerBlock169,callNormalMul,.block outerBlock170,callNormalMul,.block buildRestore]

private theorem products_wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem finish_products_machine_wp {s : State} {Q : State → Prop} :
    WP isa finishProductsMachine s Q ↔ WP isa (fieldProgram id finishProductsOps) s Q := by
  simp only [finishProductsMachine,sequence,List.foldr_cons,List.foldr_nil,
    finishProductsOps,fieldProgram,fieldCode,id,Nat.reduceEqDiff,ite_false,
    normalizeMulStep,finish_products_source169,finish_products_source170]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply products_wp_post_iff; intro t)

theorem finish_products_value {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    pointRun finishProductsOps E 2584=E 1072*E 2152*E 352 := by
  simp only [pointRun,finishProductsOps,List.foldl,PointOp.run,Function.update_apply,ite_true]
  rfl

theorem finish_products_machine_ok {base : Addr} {s : State}
    {E : Nat → Fin VG.Proof.Mont.AArch64.P521Square.fieldPrime}
    (hs : VG.Proof.Mont.AArch64.Scr s base 8192)
    (inv : OrdinaryInv base VG.Proof.Mont.AArch64.P521Square.fieldPrime id
      [1072,2152,352] E (fun _ => 1) s) :
    WP isa finishProductsMachine s fun t =>
      OrdinaryInv base VG.Proof.Mont.AArch64.P521Square.fieldPrime id
        (fieldLive finishProductsOps [1072,2152,352]) (pointRun finishProductsOps E) (fun _ => 1) t ∧
      VG.Proof.Mont.AArch64.Scr t base 8192 ∧ FieldPublic s t ∧
      FieldProgramFrame base id finishProductsOps s.mem t.mem := by
  apply finish_products_machine_wp.mpr
  exact field_program_ok (by decide) (by decide) build_field_layout finishProductsOps hs inv
    (by simp [buildSlot])
    (by simp [finishProductsOps,PointOp.out,PointOp.ins,buildSlot])
    (by decide) (by simp [finishProductsOps,fieldCoeffs])

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! ### `Weierstrass.AArch64.P521Native.FinishInverse`, which this module and modules that import it used -/

section

/-! The final inversion is the same proved ordinary/Montgomery round trip. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field (toMontValue)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native

def finishInversePhase : Prog isa := sequence [
  .block (representationMemoryCode representationToCode 1216),
  .block outerBlock167,callInvModP,.block outerBlock168,
  .block (representationMemoryCode representationFromCode 2152)]

private theorem inverse_wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem finish_inverse_phase_wp {s : State} {Q : State → Prop} :
    WP isa finishInversePhase s Q ↔ WP isa normalizeInversePhase s Q := by
  have save : outerBlock167=[.vop (.ins .d2 .v29 0 .x30)] := by decide
  have restore : outerBlock168=[.umov .x .x30 .v29 0] := by decide
  have inversion : config.pPow=.seq (.block outerBlock167) (.seq callInvModP (.block outerBlock168)) := by
    rw [save,restore]
    rfl
  simp only [finishInversePhase,normalizeInversePhase,sequence,List.foldr_cons,List.foldr_nil,inversion]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_nil_iff] | (apply inverse_wp_post_iff; intro t)

theorem finish_inverse_phase_ok (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config)
    {s : State} {base : Addr} (hs : Scr s base 8192)
    (hM : ModOkA config.MP' 8192 config.C.p s.mem base)
    (bound : wordsVal s.mem base 1216 9<fieldPrime) :
    WP isa finishInversePhase s fun t =>
      wordsVal t.mem base 2152 9<fieldPrime ∧
      Fin.ofNat fieldPrime (wordsVal t.mem base 2152 9)=
        Fin.ofNat fieldPrime (wordsVal s.mem base 1216 9)^(fieldPrime-2) ∧
      Unch base normalizeInverseWrites s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧ t.gpr .x30=s.gpr .x30 ∧ t.v .v31=s.v .v31 ∧
      wordsVal t.mem base 1216 9=toMontValue (wordsVal s.mem base 1216 9) ∧
      (∀r∈[Reg.x27,Reg.x28],t.gpr r=s.gpr r) := by
  exact finish_inverse_phase_wp.mpr (normalize_inverse_phase_ok hc hs hM bound)

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! Exact concatenation of the final independent machine-level phases. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native
open VG.Impl.Ecdsa.AArch64 (D RZ)

def finishFiveDoubles : Prog isa := .seq loop25 (.seq (.block outerBlock148) callNormalDouble)
def finishCheckCode : List Instr := config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++
  VG.Impl.Ecdh.AArch64.Cfg.finish config

def finishStages : Prog isa := sequence [
  .block outerBlock144,finishFiveDoubles,.block finishCopyPoint,finishProjectiveMachine,
  .block finishCopyPoint,.block finishFixYCode,.block finishLookupCode,finishAddMachine,
  .block finishCopyPoint,finishInversePhase,finishProductsMachine,.block finishCheckCode]

theorem finish_partition149 : outerBlock149=finishCopyPoint++outerBlock149.drop 54 := by lit_decide

theorem finish_partition152 : outerBlock152=outerBlock152.take 53++finishCopyPoint++
    finishFixYCode++finishLookupCode++outerBlock152.drop (outerBlock152.length-4) := by lit_decide

theorem finish_partition166 : outerBlock166=outerBlock166.take 53++finishCopyPoint := by lit_decide

theorem finish_partition171 : outerBlock171=buildRestore++finishCheckCode := by
  exact finish_output_source

/-- Every contract proved for the separated final phases applies to the full
exact native finishAndWrite, with no removed checks or instructions. -/
theorem finish_stages_wp {s : State} {Q : State → Prop} (h : WP isa finishStages s Q) :
    WP isa finishAndWrite s Q := by
  simp only [finishAndWrite,sequence,List.foldr_cons,List.foldr_nil]
  rw [finish_partition149,finish_partition152,finish_partition166,finish_partition171]
  simp only [finishStages,finishFiveDoubles,finishProjectiveMachine,finishAddMachine,finishInversePhase,
    finishProductsMachine,sequence,List.foldr_cons,List.foldr_nil] at h
  simp only [VG.WP.seq_iff (M:=isa),VG.WP.block_append_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)] at h ⊢
  exact h

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! Adjacent stages of the final P-521 window, sharing their machine-state interface. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

theorem finish_five_doubles_source : finishFiveDoubles=windowFiveDoubles := by
  rw [finishFiveDoubles,windowFiveDoubles,finish_doubling_loop_source,finish_counter_sources.2.2.2.2]

theorem finish_five_doubles_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (counter : s.gpr .x19=1#64) :
    WP isa (.seq (.block outerBlock144) finishFiveDoubles) s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1288=
        windowDbl (windowDbl (windowDbl (windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072))))) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧ t.gpr .x19=0#64 := by
  rw [WP.seq_iff]
  refine WP.mono (finish_counter_enter s) fun u ⟨cu,_,ku,vu⟩ => ?_
  have base : u.gpr .x0=s.gpr .x0 := ku.gpr .x0 (by decide)
  have hu : Scr u (u.gpr .x0) W := by rw [base]; exact hs.of_keeps ku (by decide)
  have bu : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [base,ku.mem]; exact bound
  have packed : u.gpr .x19=windowPacked 0 2 := by rw [cu,counter]; exact finish_counter_zero
  rw [finish_five_doubles_source]
  refine WP.mono (window_five_doubles_ok hu room bu (by decide : 0<4294967296) packed)
    fun t ⟨bt,pt,ft,kt,ct⟩ => ?_
  rw [base] at bt pt ft
  rw [ku.mem] at pt ft
  refine ⟨bt,pt,ft,?_,ct⟩
  constructor
  · exact kt.base.trans base
  · exact kt.rd.trans ku.rd
  · exact kt.wr.trans ku.wr
  · exact kt.sp.trans ku.sp
  · intro r hr h30 h19
    exact (kt.gp r hr h30 h19).trans (ku.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨h19,(by decide : ∀r∈preserved,r≠Reg.x2) r hr⟩))
  · rw [kt.v29,vu]
  · rw [kt.v31,vu]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

 theorem finish_double_frame_unch {base : Addr} {m m' : Mem} (h : WindowWorkFrame base m m') :
    Unch base [(1072,432),(4080,504)] m m' := by
  intro x hx
  exact h x (hx (1072,432) (by simp)) (hx (4080,504) (by simp))

 theorem finish_table_canonical_keep {base table : Addr} {m m' : Mem} {W : List (Nat × Nat)}
    (apart : TableWorkspaceApart base table 8192) (frame : Unch base W m m')
    (fits : ∀w∈W,w.1+w.2≤8192) (old : WindowTableCanonical m table) :
    WindowTableCanonical m' table := by
  have outside : Outside base 0 8192 m m' := frame.outside fun w hw => ⟨Nat.zero_le _,fits w hw⟩
  intro d lo hi
  rw [apart.wordsVal outside 9 (lookupEntryOffset d) (by unfold lookupEntryOffset; omega_arith),
    apart.wordsVal outside 9 (lookupEntryOffset d+72) (by unfold lookupEntryOffset; omega_arith)]
  exact old d lo hi

 theorem finish_affine_keep {base table : Addr} {m m' : Mem} {W : List (Nat × Nat)}
    (apart : TableWorkspaceApart base table 8192) (frame : Unch base W m m')
    (fits : ∀w∈W,w.1+w.2≤8192) (k j : Nat) :
    windowAffine m' table k j=windowAffine m table k j := by
  have outside : Outside base 0 8192 m m' := frame.outside fun w hw => ⟨Nat.zero_le _,fits w hw⟩
  have digit := magH_le (H:=16) (combWin_lt 5 k j)
  have xSame : windowX m' table (magH 16 (combWin 5 k j))=windowX m table (magH 16 (combWin 5 k j)) := by
    simp only [windowX]
    split
    · rfl
    · rw [apart.wordsVal outside 9 _ (by unfold lookupEntryOffset; omega_arith)]
  have ySame : windowY m' table (magH 16 (combWin 5 k j))=windowY m table (magH 16 (combWin 5 k j)) := by
    simp only [windowY]
    split
    · rfl
    · rw [apart.wordsVal outside 9 _ (by unfold lookupEntryOffset; omega_arith)]
  simp only [windowAffine,xSame,ySame]

 theorem finish_bits_keep {base : Addr} {m m' : Mem} {W : List (Nat × Nat)} {k : Nat}
    (frame : Unch base W m m') (apart : ∀w∈W,w.1+w.2≤3304 ∨ 3829≤w.1)
    (bits : ∀i<525,m (off base (3304+i))=if k.testBit i then 1 else 0) :
    ∀i<525,m' (off base (3304+i))=if k.testBit i then 1 else 0 := by
  intro i hi
  rw [frame _ (by
    intro w hw
    rw [ofs_off0 base (by omega_arith)]
    have bounds := apart w hw
    omega_arith)]
  exact bits i hi

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock144)

def finishDbl5 (P : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :=
  windowDbl (windowDbl (windowDbl (windowDbl (windowDbl P))))
def finishHomogeneous (P : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :=
  (P.1*P.2.2,(if P.2.2*P.2.2*P.2.2=0 then Fin.ofNat fieldPrime 1 else P.2.1),P.2.2*P.2.2*P.2.2)
def finishFrontReady : Prog isa :=
  .seq (.seq (.block outerBlock144) finishFiveDoubles) finishProjectivePrepare
def finishFrontWrites : List (Nat × Nat) := [(1072,432),(4080,504)]++finishProjectiveWrites

theorem finish_front_ready_ok {s : State} {table : Addr} {k : Nat}
    (hs : Scr s (s.gpr .x0) 8192) (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (counter : s.gpr .x19=1#64) (zero : wordsVal s.mem (s.gpr .x0) 280 9=0)
    (bb : wordsVal s.mem (s.gpr .x0) 568 9<fieldPrime) (oneBound : 1<fieldPrime)
    (apart : TableWorkspaceApart (s.gpr .x0) table 8192) (tableRead : LookupTableReadable s table)
    (canonical : WindowTableCanonical s.mem table)
    (bits : ∀i<525,s.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0) :
    WP isa finishFrontReady s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=finishHomogeneous (finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      Scr t (s.gpr .x0) 8192 ∧ LookupTableReadable t table ∧ WindowTableCanonical t.mem table ∧
      (∀i<525,t.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0) ∧
      wordsVal t.mem (s.gpr .x0) 280 9=0 ∧ wordsVal t.mem (s.gpr .x0) 568 9<fieldPrime ∧
      t.gpr .x19=0#64 ∧ t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧
      Unch (s.gpr .x0) finishFrontWrites s.mem t.mem ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finishFrontReady,WP.seq_iff]
  refine WP.mono (finish_five_doubles_ok hs (by decide) bound counter)
    fun u ⟨bu,pu,fu,ku,cu⟩ => ?_
  have uf := finish_double_frame_unch fu
  have hu : Scr u (s.gpr .x0) 8192 := by rw [←ku.base]; exact ku.scr hs
  have zeroU : wordsVal u.mem (s.gpr .x0) 280 9=0 := by rw [uf.wordsVal (by decide) (by decide),zero]
  refine WP.mono (finish_projective_prepare_ok hu bu zeroU oneBound)
    fun t ⟨E,ep,bt,xv,yv,zv,ez,ht,ut,c19,c20,c26,pub⟩ => ?_
  have allU : Unch (s.gpr .x0) finishFrontWrites s.mem t.mem := uf.trans ut
  have fits : ∀w∈finishFrontWrites,w.1+w.2≤8192 := by decide
  have point : ordinaryPoint t.mem (s.gpr .x0) 1072=finishHomogeneous (finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072)) := by
    have coords := ep.trans pu
    change (E 1072,E 1144,E 1216)=finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072) at coords
    rw [←coords]
    have eval := finish_projective_value E ez
    have ex := congrArg Prod.fst eval
    have ey := congrArg (fun P => P.2.1) eval
    have ezz := congrArg (fun P => P.2.2) eval
    dsimp only at ex ey ezz
    change (Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1072 9),
      Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1144 9),
      Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1216 9))=_
    rw [xv,yv,zv,ex,ey,ezz]
    rfl
  have readT : LookupTableReadable t table := by
    constructor
    · exact c26.trans ((ku.gp .x26 (by decide) (by decide) (by decide)).trans tableRead.reg)
    · intro d hd
      rw [pub.rd,pub.wr,ku.rd,ku.wr]
      exact tableRead.read d hd
  refine ⟨bt,point,ht,readT,finish_table_canonical_keep apart allU fits canonical,
    finish_bits_keep allU (by decide) bits,?_,?_,c19.trans cu,?_,?_,allU,pub.rd.trans ku.rd,pub.wr.trans ku.wr,pub.sp.trans ku.sp,?_,?_,?_⟩
  · rw [allU.wordsVal (by decide) (by decide),zero]
  · rw [allU.wordsVal (by decide) (by decide)]; exact bb
  · exact c20.trans (ku.gp .x20 (by decide) (by decide) (by decide))
  · exact c26.trans (ku.gp .x26 (by decide) (by decide) (by decide))

  · exact (pub.gpr .x27 (by decide)).trans (ku.gp .x27 (by decide) (by decide) (by decide))
  · exact (pub.gpr .x28 (by decide)).trans (ku.gp .x28 (by decide) (by decide) (by decide))
  · exact pub.v31.trans ku.v31

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! Complete final-digit group law and the existing ECDH API specification. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

def finalDouble {F : Type _} [Lean.Grind.CommRing F] (A : F×F×F) := dblJF A.1 A.2.1 A.2.2
def finalFive {F : Type _} [Lean.Grind.CommRing F] (A : F×F×F) :=
  finalDouble (finalDouble (finalDouble (finalDouble (finalDouble A))))
def finalHomogeneous {F : Type _} [Lean.Grind.CommRing F] [DecidableEq F] (A : F×F×F) :=
  (A.1*A.2.2,(if A.2.2*A.2.2*A.2.2=0 then 1 else A.2.1),A.2.2*A.2.2*A.2.2)

theorem final_five_inv {C : Curve} (law : Law C) (ha : AM3 C) {P : Point C}
    (hP : onCurve C P=true) {A : Fe C×Fe C×Fe C} {m : Nat}
    (ia : InvJ C A.1 A.2.1 A.2.2 (mul m P)) :
    InvJ C (finalFive A).1 (finalFive A).2.1 (finalFive A).2.2 (mul (32*m) P) := by
  have step {B : Fe C×Fe C×Fe C} {n : Nat} (ib : InvJ C B.1 B.2.1 B.2.2 (mul n P)) :
      InvJ C (finalDouble B).1 (finalDouble B).2.1 (finalDouble B).2.2 (mul (2*n) P) := by
    have doubled := InvJ.dbl law ha (law.onCurve_mul hP n) ib
    rw [law.add_mul_mul hP] at doubled
    have ar : n+n=2*n := by omega_arith
    rw [ar] at doubled
    exact doubled
  have i1 := step ia
  have i2 := step i1
  have i3 := step i2
  have i4 := step i3
  have i5 := step i4
  have ar : 2*(2*(2*(2*(2*m))))=32*m := by omega_arith
  rw [ar] at i5
  exact i5

theorem final_homogeneous_rep {C : Curve} (law : Law C) {A : Fe C×Fe C×Fe C} {Q : Point C}
    (ia : InvJ C A.1 A.2.1 A.2.2 Q) :
    Rep C (finalHomogeneous A).1 (finalHomogeneous A).2.1 (finalHomogeneous A).2.2 Q := by
  by_cases hz : A.2.2=0
  · have q0 := (InvJ.z_zero_iff law ia).mp hz
    rw [finalHomogeneous,hz,q0]
    simpa only [Lean.Grind.Semiring.mul_zero,ite_true] using rep_infinity' law
  · have cube := cube_ne_zero law hz
    simpa only [finalHomogeneous,cube,ite_false] using ia.rep_of_ne hz

def finalSum {C : Curve} (A D : Fe C×Fe C×Fe C) :=
  let H := finalHomogeneous (finalFive A)
  rcbAdd3 (Fin.ofNat C.p C.b) H.1 H.2.1 H.2.2 D.1 D.2.1 D.2.2

/-- The last complete addition needs no nonexceptional-point hypothesis. -/
theorem final_digit_group {C : Curve} (law : Law C) (ha : AM3 C) {P : Point C}
    (hP : onCurve C P=true) {A D : Fe C×Fe C×Fe C} {d : Nat}
    (ia : InvJ C A.1 A.2.1 A.2.2 (mul (Window5.winE (d+16*Window5.geom 105) 105 1) P))
    (id : RepA C D.1 D.2.1 D.2.2 (Window5.winPt C P (d+16*Window5.geom 105) 0)) :
    Rep C (finalSum A D).1 (finalSum A D).2.1 (finalSum A D).2.2 (mul d P) := by
  have five := final_five_inv law ha hP ia
  have homogeneous := final_homogeneous_rep law five
  have sum := law.add3 ha (law.onCurve_mul hP _) (Window5.onCurve_winPt law hP _ _) homogeneous id.1
    (show rcbAdd3 (Fin.ofNat C.p C.b) (finalHomogeneous (finalFive A)).1
      (finalHomogeneous (finalFive A)).2.1 (finalHomogeneous (finalFive A)).2.2 D.1 D.2.1 D.2.2=
      ((finalSum A D).1,(finalSum A D).2.1,(finalSum A D).2.2) from rfl)
  rw [Window5.win_add law hP (Nat.le_add_left _ _) (by decide : 0<105),Window5.winE_zero'] at sum
  exact sum

end VG.Proof.Weierstrass.AArch64.P521Native
