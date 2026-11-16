module

-- separate module: the consolidated stack/save/restore and API body replay costs 0.79s of local elaboration/kernel work versus 0.52s importing dependencies; the generic security registration reuses this whole-function functional proof.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeFront
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeWindow
public import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishInverse
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProducts
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrames
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationMath
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishChecks
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFront
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAssemble
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareSelected
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Weierstrass.Words
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishTransfer
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowGroup
public import VerifiedGarbage.Proof.Weierstrass.WindowJA
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowRun
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildGroup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeEntry
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! ### `Weierstrass.AArch64.P521Native.NativeBodyCorrectness`, which only this module used -/

section

/-! ### `Weierstrass.AArch64.P521Native.Finish`, which only this module used -/

section

/-! Adjacent stages of the final P-521 window, sharing their machine-state interface. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field (OrdinaryInv pointRun toMontValue)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

def finalizeCore : Prog isa := .seq (.block finishCopyPoint) (.seq finishInversePhase finishProductsMachine)
def finalizeWrites : List (Nat × Nat) :=
  [(1072,72),(1144,72),(1216,72)]++normalizeInverseWrites++fieldProgramWrites id finishProductsOps

theorem finalize_core_ok (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config)
    {base : Addr} {s : State} (hs : Scr s base 8192)
    (hM : ModOkA config.MP' 8192 config.C.p s.mem base)
    (bounds : ∀d∈[1288,1360,1432,352],wordsVal s.mem base d 9<fieldPrime) :
    WP isa finalizeCore s fun t =>
      Scr t base 8192 ∧ wordsVal t.mem base 2584 9<fieldPrime ∧
      Fin.ofNat fieldPrime (wordsVal t.mem base 2584 9)=
        Fin.ofNat fieldPrime (wordsVal s.mem base 1288 9)*
        Fin.ofNat fieldPrime (wordsVal s.mem base 1432 9)^(fieldPrime-2)*
        Fin.ofNat fieldPrime (wordsVal s.mem base 352 9) ∧
      wordsVal t.mem base 1216 9=toMontValue (wordsVal s.mem base 1432 9) ∧
      Unch base finalizeWrites s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧ t.gpr .x30=s.gpr .x30 ∧
      t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finalizeCore,WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (finish_copy_point_ok hs)) fun u ⟨⟨xu,yu,zu,ku,uc⟩,vu⟩ => ?_
  obtain hu := hs.of_keepRegs ku (by decide)
  obtain Mu : ModOkA config.MP' 8192 config.C.p u.mem base := {hM with val:=by rw [uc.wordsVal (by decide) (by decide)]; exact hM.val}
  obtain bu : wordsVal u.mem base 1216 9<fieldPrime := by rw [zu]; exact bounds 1432 (by simp)
  rw [WP.seq_iff]
  refine WP.mono (finish_inverse_phase_ok hc hu Mu bu)
    fun v ⟨invBound,invValue,uv,zero,rd,wr,sp,g20,g26,g30,v31,converted,gExtra⟩ => ?_
  obtain hv : Scr v base 8192 := ⟨zero,by rw [wr]; exact hu.wr,hu.nowrap,hu.enc⟩
  obtain xSame : wordsVal v.mem base 1072 9=wordsVal s.mem base 1288 9 := by
    rw [uv.wordsVal (by decide) (by decide),xu]
  obtain oneSame : wordsVal v.mem base 352 9=wordsVal s.mem base 352 9 := by
    rw [uv.wordsVal (by decide) (by decide),uc.wordsVal (by decide) (by decide)]
  let E : Nat → Fin fieldPrime := fun d => Fin.ofNat fieldPrime (wordsVal v.mem base d 9)
  obtain live : OrdinaryInv base fieldPrime id [1072,2152,352] E (fun _ => 1) v := by
    constructor
    · intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl
      · simpa only [id_eq,Nat.one_mul,xSame] using bounds 1288 (by simp)
      · simpa only [id_eq,Nat.one_mul] using invBound
      · simpa only [id_eq,Nat.one_mul,oneSame] using bounds 352 (by simp)
    · intro d _; rfl
  refine WP.mono (finish_products_machine_ok hv live) fun t ⟨it,ht,kt,ft⟩ => ?_
  obtain productsU := field_program_frame_unch ft
  obtain allU : Unch base finalizeWrites s.mem t.mem := uc.trans (uv.trans productsU)
  obtain outBound := it.bound 2584 (by decide)
  obtain outValue := it.value 2584 (by decide)
  rw [finish_products_value] at outValue
  change Fin.ofNat fieldPrime (wordsVal t.mem base 2584 9)=
    Fin.ofNat fieldPrime (wordsVal v.mem base 1072 9)*
    Fin.ofNat fieldPrime (wordsVal v.mem base 2152 9)*
    Fin.ofNat fieldPrime (wordsVal v.mem base 352 9) at outValue
  rw [xSame,invValue,zu,oneSame] at outValue
  refine ⟨ht,by simpa only [id_eq,Nat.one_mul] using outBound,outValue,?_,allU,?_,
    kt.rd.trans (rd.trans ku.rd),kt.wr.trans (wr.trans ku.wr),kt.sp.trans (sp.trans ku.sp),?_,?_,?_,?_,?_,?_⟩
  · rw [productsU.wordsVal (by decide) (by decide),converted,zu]
  · exact ht.x0
  · exact (kt.gpr .x20 (by decide)).trans (g20.trans (ku.gpr .x20 (by decide)))
  · exact (kt.gpr .x26 (by decide)).trans (g26.trans (ku.gpr .x26 (by decide)))
  · exact (kt.gpr .x30 (by decide)).trans (g30.trans (ku.gpr .x30 (by decide)))
  · exact (kt.gpr .x27 (by decide)).trans ((gExtra .x27 (by simp)).trans (ku.gpr .x27 (by decide)))
  · exact (kt.gpr .x28 (by decide)).trans ((gExtra .x28 (by simp)).trans (ku.gpr .x28 (by decide)))
  · exact kt.v31.trans (v31.trans (congrFun vu .v31))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64.P521Field (toMontValue_zero_iff)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

def finishFinal : Prog isa := .seq finalizeCore (.block
  (config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++VG.Impl.Ecdh.AArch64.Cfg.finish config))

def finishAccept (base : Addr) (s : State) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0<wordsVal s.mem base 2368 9 ∧ wordsVal s.mem base 2368 9<config.C.n) ∧
    wordsVal s.mem base 1432 9≠0)

theorem finish_final_ok (hc : BaseCfgOk config) {base : Addr} {s : State}
    (hs : Scr s base 8192) (hM : ModOkA config.MP' 8192 config.C.p s.mem base)
    (bounds : ∀d∈[1288,1360,1432,352],wordsVal s.mem base d 9<fieldPrime)
    {g : Reg → BitVec 64} (saved : Spill.Saved base g Cfg.saved s.mem)
    (mn : wordsVal s.mem base 136 9=config.C.n)
    {V : Prop} [Decidable V] (flag : word s.mem base 3232=mask V) {out : Addr}
    (outReg : s.gpr .x20=out) (outFit : out.toNat+66≤2^64)
    (outW : (⟨out,66⟩ : Region)∈s.wr) (outApart : Region.Disjoint ⟨out,66⟩ ⟨base,8192⟩) :
    WP isa finishFinal s fun t => ∃xv,xv<fieldPrime ∧
      Fin.ofNat fieldPrime xv=
        Fin.ofNat fieldPrime (wordsVal s.mem base 1288 9)*
        Fin.ofNat fieldPrime (wordsVal s.mem base 1432 9)^(fieldPrime-2)*
        Fin.ofNat fieldPrime (wordsVal s.mem base 352 9) ∧
      VG.Spec.Ecdsa.bytesAt t.mem out 66=(if finishAccept base s V then VG.Spec.Weierstrass.toBytes 66 xv else List.replicate 66 0) ∧
      (t.gpr .x0).setWidth 32=(if finishAccept base s V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finishFinal,WP.seq_iff]
  refine WP.mono (finalize_core_ok hc hs hM bounds)
    fun u ⟨hu,bound,value,converted,frame,zero,rd,wr,sp,g20,g26,g30,g27,g28,v31⟩ => ?_
  obtain mnu : wordsVal u.mem base 136 9=config.C.n := by
    rw [frame.wordsVal (by decide) (by decide)]; exact mn
  obtain savedU := Saved.unch saved (W:=finalizeWrites) (by decide) frame
  obtain flagU : word u.mem base 3232=mask V := by
    rw [frame.word (by decide) (by decide)]; exact flag
  obtain outU : u.gpr .x20=out := g20.trans outReg
  obtain wrU : (⟨out,66⟩ : Region)∈u.wr := by rw [wr]; exact outW
  obtain dSame : wordsVal u.mem base 2368 9=wordsVal s.mem base 2368 9 := frame.wordsVal (by decide) (by decide)
  obtain accept : VG.Proof.Ecdh.AArch64.ok config base u V=finishAccept base s V := by
    simp only [VG.Proof.Ecdh.AArch64.ok,sv,finishAccept,
      (show config.n=9 from rfl),(show config.sl D=2368 from rfl),(show config.sl RZ=1216 from rfl)]
    rw [dSame,converted]
    simp only [ne_eq,toMontValue_zero_iff (bounds 1432 (by simp))]
  obtain ⟨trace,t,exec,bytes,ret,restored⟩ := checked_finish_ok hc hu mnu savedU flagU outU outFit wrU outApart
  let code : List Instr := config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++VG.Impl.Ecdh.AArch64.Cfg.finish config
  obtain check27 : code.all (fun i => decide (clobbers i .x27=false))=true := by lit_decide
  obtain check28 : code.all (fun i => decide (clobbers i .x28=false))=true := by lit_decide
  obtain checkV : code.all (fun i => decide (vdstOf i≠some .v31))=true := by lit_decide
  obtain hc27 : ∀i∈instrs (.block code : Prog isa),clobbers i .x27=false := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using check27
  obtain hc28 : ∀i∈instrs (.block code : Prog isa),clobbers i .x28=false := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using check28
  obtain hcV : ∀i∈instrs (.block code : Prog isa),vdstOf i≠some .v31 := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using checkV
  obtain regions := Exec.rdwr exec
  refine ⟨trace,t,exec,_,bound,value,?_,?_,restored,regions.1.trans rd,regions.2.1.trans wr,regions.2.2.trans sp,
    (Exec.gpr hc27 exec).trans g27,(Exec.gpr hc28 exec).trans g28,(Exec.vec hcV exec).trans v31⟩
  · simpa only [(show config.C.len=66 from rfl),sv,(show config.n=9 from rfl),
      (show config.sl X=2584 from rfl),accept] using bytes
  · rw [ret,accept]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config finishAndWrite)

structure FinishPre (s : State) (table : Addr) (k : Nat) (g : Reg → BitVec 64) (V : Prop) [Decidable V] (out : Addr) : Prop where
  workspace : Scr s (s.gpr .x0) 8192
  point : canonicalPoint s.mem (s.gpr .x0) 1072
  counter : s.gpr .x19=1#64
  zero : wordsVal s.mem (s.gpr .x0) 280 9=0
  b : wordsVal s.mem (s.gpr .x0) 568 9<fieldPrime
  oneBound : wordsVal s.mem (s.gpr .x0) 352 9<fieldPrime
  fieldOne : 1<fieldPrime
  tableApart : TableWorkspaceApart (s.gpr .x0) table 8192
  tableRead : LookupTableReadable s table
  tableCanonical : WindowTableCanonical s.mem table
  bits : ∀i<525,s.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0
  modulus : ModOkA config.MP' 8192 config.C.p s.mem (s.gpr .x0)
  order : wordsVal s.mem (s.gpr .x0) 136 9=config.C.n
  saved : Spill.Saved (s.gpr .x0) g Cfg.saved s.mem
  flag : word s.mem (s.gpr .x0) 3232=mask V
  outReg : s.gpr .x20=out
  outFit : out.toNat+66≤2^64
  outW : (⟨out,66⟩ : Region)∈s.wr
  outApart : Region.Disjoint ⟨out,66⟩ ⟨s.gpr .x0,8192⟩

def finishFullAccept (s : State) (table : Addr) (k : Nat) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0<wordsVal s.mem (s.gpr .x0) 2368 9 ∧ wordsVal s.mem (s.gpr .x0) 2368 9<config.C.n) ∧
    (finishSum s.mem (s.gpr .x0) table k).2.2≠0)

def finishPhases : Prog isa := .seq finishFront finishFinal

theorem finish_phases_wp {s : State} {Q : State → Prop} (h : WP isa finishPhases s Q) :
    WP isa finishAndWrite s Q := by
  apply finish_stages_wp
  simp only [finishPhases,finishFront,finishFrontReady,finishProjectivePrepare,finishSelectedSum,
    finishFinal,finalizeCore,finishStages,finishCheckCode,
    VG.Impl.Weierstrass.AArch64.P521Native.sequence,List.foldr_cons,List.foldr_nil] at h ⊢
  simp only [VG.WP.seq_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)] at h ⊢
  exact h

theorem finish_ok (hc : BaseCfgOk config) {s : State} {table : Addr} {k : Nat}
    {g : Reg → BitVec 64} {V : Prop} [Decidable V] {out : Addr} (pre : FinishPre s table k g V out) :
    WP isa finishAndWrite s fun t => ∃xv,xv<fieldPrime ∧
      Fin.ofNat fieldPrime xv=(finishSum s.mem (s.gpr .x0) table k).1*
        (finishSum s.mem (s.gpr .x0) table k).2.2^(fieldPrime-2)*
        Fin.ofNat fieldPrime (wordsVal s.mem (s.gpr .x0) 352 9) ∧
      VG.Spec.Ecdsa.bytesAt t.mem out 66=(if finishFullAccept s table k V then VG.Spec.Weierstrass.toBytes 66 xv else List.replicate 66 0) ∧
      (t.gpr .x0).setWidth 32=(if finishFullAccept s table k V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  apply finish_phases_wp
  rw [finishPhases,WP.seq_iff]
  refine WP.mono (finish_front_ok pre.workspace pre.point pre.counter pre.zero pre.b pre.fieldOne
    pre.tableApart pre.tableRead pre.tableCanonical pre.bits)
    fun u ⟨bu,pu,hu,frame,rd,wr,sp,g20,g26,g27,g28,v31⟩ => ?_
  obtain Mu : ModOkA config.MP' 8192 config.C.p u.mem (s.gpr .x0) :=
    {pre.modulus with val:=by rw [frame.wordsVal (by decide) (by decide)]; exact pre.modulus.val}
  obtain oneSame : wordsVal u.mem (s.gpr .x0) 352 9=wordsVal s.mem (s.gpr .x0) 352 9 := frame.wordsVal (by decide) (by decide)
  obtain bounds : ∀d∈[1288,1360,1432,352],wordsVal u.mem (s.gpr .x0) d 9<fieldPrime := by
    intro d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl
    · exact bu.1
    · exact bu.2.1
    · exact bu.2.2
    · rw [oneSame]; exact pre.oneBound
  obtain savedU := Saved.unch pre.saved (W:=finishAllFrontWrites) (by decide) frame
  obtain mnU : wordsVal u.mem (s.gpr .x0) 136 9=config.C.n := by rw [frame.wordsVal (by decide) (by decide)]; exact pre.order
  obtain flagU : word u.mem (s.gpr .x0) 3232=mask V := by rw [frame.word (by decide) (by decide)]; exact pre.flag
  obtain outU : u.gpr .x20=out := g20.trans pre.outReg
  obtain wrU : (⟨out,66⟩ : Region)∈u.wr := by rw [wr]; exact pre.outW
  obtain dSame : wordsVal u.mem (s.gpr .x0) 2368 9=wordsVal s.mem (s.gpr .x0) 2368 9 := frame.wordsVal (by decide) (by decide)
  obtain px := congrArg Prod.fst pu
  obtain pz := congrArg (fun P => P.2.2) pu
  dsimp only [ordinaryPoint] at px pz
  obtain accept : finishAccept (s.gpr .x0) u V=finishFullAccept s table k V := by
    simp only [finishAccept,finishFullAccept,dSame]
    rw [decide_eq_decide]
    apply and_congr_right
    intro _
    apply not_congr
    exact (canonical_fin_zero bu.2.2).symm.trans (by rw [pz])
  refine WP.mono (finish_final_ok hc hu Mu bounds savedU mnU flagU outU pre.outFit wrU pre.outApart)
    fun t ⟨xv,xb,value,bytes,ret,restore,rdT,wrT,spT,g27T,g28T,v31T⟩ => ?_
  rw [px,pz,oneSame] at value
  exact ⟨xv,xb,value,by rw [bytes,accept],by rw [ret,accept],restore,rdT.trans rd,wrT.trans wr,spT.trans sp,g27T.trans g27,g28T.trans g28,v31T.trans v31⟩

private theorem finite_one {p : Nat} [NeZero p] : Fin.ofNat p 1=(1 : Fin p) := rfl

theorem finish_ok_one (hc : BaseCfgOk config) {s : State} {table : Addr} {k : Nat}
    {g : Reg → BitVec 64} {V : Prop} [Decidable V] {out : Addr} (pre : FinishPre s table k g V out)
    (one : wordsVal s.mem (s.gpr .x0) 352 9=1) :
    WP isa finishAndWrite s fun t => ∃xv,xv<fieldPrime ∧
      Fin.ofNat fieldPrime xv=(finishSum s.mem (s.gpr .x0) table k).1*
        (finishSum s.mem (s.gpr .x0) table k).2.2^(fieldPrime-2) ∧
      VG.Spec.Ecdsa.bytesAt t.mem out 66=(if finishFullAccept s table k V then VG.Spec.Weierstrass.toBytes 66 xv else List.replicate 66 0) ∧
      (t.gpr .x0).setWidth 32=(if finishFullAccept s table k V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  refine WP.mono (finish_ok hc pre) fun t ⟨xv,xb,value,bytes,ret,restore,rd,wr,sp,g27,g28,v31⟩ => ?_
  obtain oneFin : Fin.ofNat fieldPrime (wordsVal s.mem (s.gpr .x0) 352 9)=(1 : Fin fieldPrime) := by
    rw [one]
    exact finite_one
  rw [oneFin,Lean.Grind.Semiring.mul_one] at value
  exact ⟨xv,xb,value,bytes,ret,restore,rd,wr,sp,g27,g28,v31⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end


end

/-! ### `Weierstrass.AArch64.P521Native.WindowAffineGroup`, which only this module used -/

section

/-! Affine table entries and secret signed magnitudes represent the window's point. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass

 def windowAffineN (p : Nat) [NeZero p] (m : Mem) (table : Addr) (k j : Nat) : Fin p×Fin p×Fin p :=
  let d := magH 16 (combWin 5 k j)
  (Fin.ofNat p (windowX m table d),
   Fin.ofNat p (if combWin 5 k j<16 then (p-windowY m table d)%p else windowY m table d),
   Fin.ofNat p (if d=0 then 0 else 1))

 theorem window_comb_five (k j : Nat) : combWin 5 k j=Window5.nib k j := by
  simp only [combWin,Window5.nib]
  rw [Nat.pow_mul]

 theorem window_neg_cast {p y : Nat} [NeZero p] (hy : y<p) :
    Fin.ofNat p ((p-y)%p)=-(Fin.ofNat p y) := by
  apply Fin.ext
  simp only [Fin.val_ofNat,Fin.neg_def,Nat.mod_mod,Nat.mod_eq_of_lt hy]

 theorem window_affine_group {C : Curve} (law : Law C) {P : Point C}
    (m : Mem) (table : Addr) (k j : Nat)
    (canonical : ∀d,1≤d → d≤16 → wordsVal m table (lookupEntryOffset d+72) 9<C.p)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d+72) 9)) 1 (mul d P)) :
    Rep C (windowAffineN C.p m table k j).1 (windowAffineN C.p m table k j).2.1
      (windowAffineN C.p m table k j).2.2 (Window5.winPt C P k j) := by
  let v := combWin 5 k j
  let d := magH 16 v
  obtain hv : v<32 := combWin_lt 5 k j
  obtain hd : d≤16 := magH_le hv
  obtain win : Window5.winPt C P k j=if 16≤v then mul (v-16) P else negPt (mul (16-v) P) := by
    rw [Window5.winPt,←window_comb_five]
  by_cases hd0 : d=0
  · have v16 : v=16 := by
      dsimp only [d] at hd0
      unfold magH at hd0
      split at hd0 <;> omega_arith
    have zeroDigit : magH 16 (combWin 5 k j)=0 := hd0
    simp only [windowAffineN,windowX,windowY,zeroDigit,ite_true]
    rw [win]
    change Rep C 0 (Fin.ofNat C.p (if v<16 then (C.p-1)%C.p else 1)) 0
      (if 16≤v then mul (v-16) P else negPt (mul (16-v) P))
    simp only [v16,Nat.lt_irrefl,ite_false,Nat.le_refl,ite_true,Nat.sub_self,Window5.mul_zero_pt]
    exact ⟨rfl,law.one_ne_zero,rfl⟩
  · have h1 : 1≤d := by omega_arith
    obtain entry := entries d h1 hd
    have zeroDigit : magH 16 (combWin 5 k j)≠0 := hd0
    by_cases negative : v<16
    · have dm : d=16-v := by dsimp only [d]; unfold magH; rw [ite_eq_right (by omega_arith)]
      obtain nc := window_neg_cast (canonical d h1 hd)
      have negEntry := entry.negY
      rw [windowAffineN,win]
      simp only [windowX,windowY,zeroDigit,ite_false]
      change Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
        (Fin.ofNat C.p (if v<16 then (C.p-wordsVal m table (lookupEntryOffset d+72) 9)%C.p
          else wordsVal m table (lookupEntryOffset d+72) 9)) 1
        (if 16≤v then mul (v-16) P else negPt (mul (16-v) P))
      rw [ite_eq_left negative,ite_eq_right (by omega_arith),nc,←dm]
      exact negEntry
    · have dm : d=v-16 := by dsimp only [d]; unfold magH; rw [ite_eq_left (by omega_arith)]
      rw [windowAffineN,win]
      simp only [windowX,windowY,zeroDigit,ite_false]
      change Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
        (Fin.ofNat C.p (if v<16 then (C.p-wordsVal m table (lookupEntryOffset d+72) 9)%C.p
          else wordsVal m table (lookupEntryOffset d+72) 9)) 1
        (if 16≤v then mul (v-16) P else negPt (mul (16-v) P))
      rw [ite_eq_right negative,ite_eq_left (by omega_arith),←dm]
      exact entry

 theorem window_affine_normalized {p : Nat} [NeZero p] (m : Mem) (table : Addr) (k j : Nat) :
    (windowAffineN p m table k j).2.2=1 ∨ (windowAffineN p m table k j).2.2=0 := by
  by_cases h : magH 16 (combWin 5 k j)=0
  · right; simp only [windowAffineN,h,ite_true]; rfl
  · left; simp only [windowAffineN,h,ite_false]; rfl

 theorem window_affine_repA {C : Curve} (law : Law C) {P : Point C}
    (m : Mem) (table : Addr) (k j : Nat)
    (canonical : ∀d,1≤d → d≤16 → wordsVal m table (lookupEntryOffset d+72) 9<C.p)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d+72) 9)) 1 (mul d P)) :
    RepA C (windowAffineN C.p m table k j).1 (windowAffineN C.p m table k j).2.1
      (windowAffineN C.p m table k j).2.2 (Window5.winPt C P k j) :=
  ⟨window_affine_group law m table k j canonical entries,window_affine_normalized m table k j⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

end


@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

 def windowDoublesF {F : Type _} [Lean.Grind.CommRing F] : Nat → (F×F×F) → (F×F×F)
  | 0,A => A
  | n+1,A => let D := windowDoublesF n A; dblJF D.1 D.2.1 D.2.2

 def windowNonfinalF {F : Type _} [Lean.Grind.CommRing F] [DecidableEq F] (E : Nat → F×F×F) :
    Nat → (F×F×F) → (F×F×F)
  | 0,A => A
  | j+1,A => windowNonfinalF E j (windowSelectF (windowDoublesF 5 A) (E (j+1)))

 theorem window_doubles_group {C : Curve} (law : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) (e n : Nat) {A : Fe C×Fe C×Fe C}
    (current : InvJ C A.1 A.2.1 A.2.2 (mul e P)) :
    InvJ C (windowDoublesF n A).1 (windowDoublesF n A).2.1 (windowDoublesF n A).2.2 (mul (2^n*e) P) := by
  induction n with
  | zero => simpa only [windowDoublesF,Nat.pow_zero,Nat.one_mul] using current
  | succ n ih =>
    obtain doubled := InvJ.dbl law ha (law.onCurve_mul hP (2^n*e)) ih
    rw [law.add_mul_mul hP] at doubled
    obtain same : 2^n*e+2^n*e=2^(n+1)*e := by rw [Nat.pow_succ,Nat.mul_two,Nat.add_mul]
    rw [same] at doubled
    exact doubled

 theorem window_nonfinal_group {C : Curve} (law : Law C) (ha : AM3 C) (order : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (nonzero : P≠.infinity) (hn : 64≤C.n)
    {k J : Nat} (hk : k<C.n) (E : Nat → Fe C×Fe C×Fe C)
    (entries : ∀j,1≤j → j<J → InvJ C (E j).1 (E j).2.1 (E j).2.2
      (Window5.winPt C P (k+16*Window5.geom J) j))
    (affine : ∀j,1≤j → j<J → (E j).2.2=0 ∨ (E j).2.2=1) :
    ∀(n : Nat) (A : Fe C×Fe C×Fe C),n<J →
      InvJ C A.1 A.2.1 A.2.2 (mul (Window5.winE (k+16*Window5.geom J) J (n+1)) P) →
      InvJ C (windowNonfinalF E n A).1 (windowNonfinalF E n A).2.1 (windowNonfinalF E n A).2.2
        (mul (Window5.winE (k+16*Window5.geom J) J 1) P)
  | 0,A,_,current => current
  | n+1,A,top,current => by
    let e := Window5.winE (k+16*Window5.geom J) J (n+2)
    obtain doubled := window_doubles_group law ha hP e 5 current
    change InvJ C (windowDoublesF 5 A).1 (windowDoublesF 5 A).2.1 (windowDoublesF 5 A).2.2 (mul (32*e) P) at doubled
    obtain hQ := law.onCurve_mul hP (32*e)
    obtain hS := Window5.onCurve_winPt law hP (k+16*Window5.geom J) (n+1)
    obtain different : mul (32*e) P≠.infinity → Window5.winPt C P (k+16*Window5.geom J) (n+1)≠.infinity →
        mul (32*e) P≠Window5.winPt C P (k+16*Window5.geom J) (n+1) := by
      intro hQ0 _
      obtain he : 1≤e := by
        by_contra h
        obtain e0 : e=0 := by omega_arith
        rw [e0,Nat.mul_zero,Window5.mul_zero_pt] at hQ0
        exact hQ0 rfl
      exact (window_noexc_nonfinal law order hP nonzero hn hk top (by omega_arith) he).1
    obtain step := window_select_group law ha (A:=windowDoublesF 5 A) (E:=E (n+1)) hQ hS doubled
      (entries (n+1) (by omega_arith) top) (affine (n+1) (by omega_arith) top) different
    obtain w := Window5.win_add law hP (k:=k+16*Window5.geom J) (J:=J) (j:=n+1) (Nat.le_add_left _ _) top
    change Spec.Weierstrass.add (mul (32*e) P) (Window5.winPt C P (k+16*Window5.geom J) (n+1))=_ at w
    rw [w] at step
    exact window_nonfinal_group law ha order hP nonzero hn hk E entries affine n _ (by omega_arith) step

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

-- Keep the doubling formula opaque while comparing its fivefold iteration.
private theorem window_doubles_step (n : Nat) (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowDoublesF (n+1) A=windowDbl (windowDoublesF n A) := rfl

 theorem window_five_generic (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowFiveValue A=windowDoublesF 5 A := by
  unfold windowFiveValue
  rw [window_doubles_step,window_doubles_step,window_doubles_step,window_doubles_step,window_doubles_step]
  rfl

 theorem window_affine_generic (m : Mem) (table : Addr) (k j : Nat) :
    windowAffine m table k j=windowAffineN fieldPrime m table k j := rfl

 theorem window_run_generic (m : Mem) (table : Addr) (k n : Nat) (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowNonfinal m table k n A=windowNonfinalF (fun j => windowAffineN fieldPrime m table k j) n A := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    simp only [windowNonfinal,windowNonfinalF,ih,windowStepValue,window_five_generic,window_affine_generic]

 theorem window_run_group_transfer {C : Curve} {p : Nat} [NeZero p]
    (hp : C.p=p) (law : Law C) (ha : AM3 C) (order : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (nonzero : P≠.infinity) (hn : 64≤C.n)
    {k steps : Nat} (hk : k<C.n) (hSteps : steps<105) (m : Mem) (table : Addr)
    {AX AY AZ OX OY OZ : Nat}
    (value : (Fin.ofNat p OX,Fin.ofNat p OY,Fin.ofNat p OZ)=
      windowNonfinalF (fun j => windowAffineN p m table (k+16*Window5.geom 105) j) steps
        (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ))
    (canonical : ∀d,1≤d → d≤16 → wordsVal m table (lookupEntryOffset d+72) 9<C.p)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d+72) 9)) 1 (mul d P))
    (current : InvJ C (Fin.ofNat C.p AX) (Fin.ofNat C.p AY) (Fin.ofNat C.p AZ)
      (mul (Window5.winE (k+16*Window5.geom 105) 105 (steps+1)) P)) :
    InvJ C (Fin.ofNat C.p OX) (Fin.ofNat C.p OY) (Fin.ofNat C.p OZ)
      (mul (Window5.winE (k+16*Window5.geom 105) 105 1) P) := by
  rcases C with ⟨q,a,b,gx,gy,n,len,qnz,nnz⟩
  dsimp only at hp
  subst q
  let E := fun j => windowAffineN p m table (k+16*Window5.geom 105) j
  have reps (j : Nat) := window_affine_repA law m table (k+16*Window5.geom 105) j canonical entries
  obtain invs : ∀j,1≤j → j<105 → InvJ _ (E j).1 (E j).2.1 (E j).2.2
      (Window5.winPt _ P (k+16*Window5.geom 105) j) := by
    intro j _ _
    exact InvJ.of_rep01 (reps j).1 (reps j).2
  obtain zs : ∀j,1≤j → j<105 → (E j).2.2=0 ∨ (E j).2.2=1 := by
    intro j _ _
    exact (reps j).2.symm
  change (Fin.ofNat p OX,Fin.ofNat p OY,Fin.ofNat p OZ)=
    windowNonfinalF E steps (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ) at value
  obtain result := window_nonfinal_group law ha order hP nonzero hn hk E invs zs steps
    (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ) hSteps current
  rw [←value] at result
  exact result

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime montBase)
open VG.Impl.Weierstrass.AArch64.P521Native (config)
open Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

abbrev nativeScalar (s : State) := ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) 66)
abbrev nativePeerBytes (s : State) := Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) 133

private theorem NativeApiDecode_native_prime : config.C.p=fieldPrime := by
  dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,Spec.P521.curve,Spec.P521.p,fieldPrime]
private theorem NativeApiDecode_native_radix : 2^(64*config.n)=montBase := by
  dsimp only [montBase]
  congr 1
private theorem NativeApiDecode_field_relabel {p q R S n a : Nat} [NeZero p] [NeZero q]
    (hp : p=q) (hr : R=S) (h : Fin.ofNat q n=toM q S a) : Fin.ofNat p n=toM p R a := by
  cases hp
  cases hr
  exact h

theorem native_api_decode {s args loaded ready : State} {P : Point config.C}
    (pre : PrepareStackPre s)
    (keep : Keeps [.x2,.x3,.x4,.x6,.x26] (allocated 3456 s) args)
    (stage : St₁ config none args (s.gpr .x3) loaded)
    (core : PrepareCorePost args loaded (s.gpr .x3) (s.gpr .x2) ready)
    (privateArg : args.gpr .x3=s.gpr .x1) (peerPlus : args.gpr .x2=s.gpr .x2+BitVec.ofNat 64 1)
    (selected : peerPoint config.C ready.mem (s.gpr .x3)=P) :
    ∃x y,
      ofBytes (((nativePeerBytes s).drop 1).take config.C.len)=x ∧
      ofBytes ((nativePeerBytes s).drop (config.C.len+1))=y ∧
      word ready.mem (s.gpr .x3) 3232=mask (VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y) ∧
      (∀h : VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y,P=.affine ⟨x,h.2.1⟩ ⟨y,h.2.2.1⟩) ∧
      wordsVal ready.mem (s.gpr .x3) 2368 9=nativeScalar s ∧
      wordsVal ready.mem (s.gpr .x3) 3944 10=nativeScalar s%2^521+recodeOffset := by
  obtain ⟨peer,checked,_,_,fields,offset,_,original,_,_,_,_,flag,px,py,_,_,_,peerX,peerY⟩ := core
  obtain loadedFrame : Outside (s.gpr .x3) 0 8192 s.mem loaded.mem := fun x hx =>
    (stage.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun keep.mem x)
  obtain tagSame : loaded.mem (s.gpr .x2)=s.mem (s.gpr .x2) := by
    obtain h := keep_of_disjoint' loadedFrame pre.args.peer_apart (by decide) (i:=0) (by decide) (by decide)
    simpa only [BitVec.add_zero] using h
  obtain xParsed : ofBytes (((nativePeerBytes s).drop 1).take config.C.len)=sv config (s.gpr .x3) peer E := by
    change ofBytes (((Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1+2*config.C.len)).drop 1).take config.C.len)=_
    rw [VG.Proof.Ecdh.AArch64.peer_bytes,List.drop_one,List.tail_cons,List.take_left' (length_bytesAt _ _ _),
      peerX,stage.e,shAt_none,Nat.shiftRight_zero]
    simp only [ev,keep.mem,peerPlus]
    rfl
  obtain yParsed : ofBytes ((nativePeerBytes s).drop (config.C.len+1))=sv config (s.gpr .x3) peer QY := by
    change ofBytes ((Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1+2*config.C.len)).drop (config.C.len+1))=_
    rw [VG.Proof.Ecdh.AArch64.peer_bytes,List.drop_succ_cons,List.drop_left' (length_bytesAt _ _ _),peerY,
      bytesAt_keep loadedFrame (pre.args.peer_apart.sub_left (Offset.sub_base _ (by decide))) (by decide) (by decide)]
  obtain guard : prepareCoreValid (s.gpr .x3) loaded peer (s.gpr .x2) ↔
      VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) (sv config (s.gpr .x3) peer E) (sv config (s.gpr .x3) peer QY) := by
    simp only [prepareCoreValid,VG.Proof.Ecdh.AArch64.PeerOk,tagSame,VG.Proof.Ecdh.Valid]
    constructor
    · rintro ⟨⟨⟨tag,xb⟩,yb⟩,curve⟩; exact ⟨tag,xb,yb,curve⟩
    · rintro ⟨tag,xb,yb,curve⟩; exact ⟨⟨⟨tag,xb⟩,yb⟩,curve⟩
  obtain xReady := (NativeApiDecode_field_relabel NativeApiDecode_native_prime NativeApiDecode_native_radix (fields 2800 (by decide)).2).trans px
  obtain yReady := (NativeApiDecode_field_relabel NativeApiDecode_native_prime NativeApiDecode_native_radix (fields 3160 (by decide)).2).trans py
  obtain dLoaded : wordsVal loaded.mem (s.gpr .x3) 2368 9=nativeScalar s := by
    have h := stage.d
    rw [shAt_none,Nat.shiftRight_zero] at h
    simp only [dv,keep.mem,keep.gpr .x1 (by decide)] at h
    exact h
  obtain kLoaded : wordsVal loaded.mem (s.gpr .x3) 2296 9=nativeScalar s := by
    have h := stage.k
    simp only [kv,keep.mem,privateArg] at h
    exact h
  refine ⟨_,_,xParsed,yParsed,?_,?_,original.trans dLoaded,?_⟩
  · simpa only [mask,guard] using flag
  · intro valid
    obtain hg := guard.mpr valid
    rw [ite_eq_left hg] at xReady yReady
    rw [←selected]
    exact congrArg₂ (@Point.affine config.C) (VG.Proof.EcKey.fe_eq valid.2.1 xReady)
      (VG.Proof.EcKey.fe_eq valid.2.2.1 yReady)
  · rw [offset,kLoaded]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

 theorem window_affine_at_eq (C : Curve) (m : Mem) (table : Addr) (k j : Nat) :
    windowAffineAt C m table k j=windowAffineN C.p m table k j := rfl

 theorem finish_sum_table_rep {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    {m : Mem} {base table : Addr} {d k : Nat} (offset : k=d+16*Window5.geom 105)
    {P : Point C} (hP : onCurve C P=true)
    (b : Fin.ofNat C.p (wordsVal m base 568 9)=Fin.ofNat C.p C.b)
    (current : InvJ C (pointAt C m base 1072).1 (pointAt C m base 1072).2.1 (pointAt C m base 1072).2.2
      (mul (Window5.winE k 105 1) P))
    (canonical : WindowTableCanonical m table)
    (rows : ∀i,i<16 → Rep C (Fin.ofNat C.p (wordsVal m table (216*i) 9))
      (Fin.ofNat C.p (wordsVal m table (216*i+72) 9)) 1 (mul (i+1) P)) :
    Rep C (finishSumAt C m base table k).1 (finishSumAt C m base table k).2.1
      (finishSumAt C m base table k).2.2 (mul d P) := by
  obtain yBound : ∀j,1≤j → j≤16 → wordsVal m table (lookupEntryOffset j+72) 9<C.p := by
    intro j lo hi
    rw [hp]
    exact (canonical j lo hi).2
  obtain entries : ∀j,1≤j → j≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset j) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset j+72) 9)) 1 (mul j P) := by
    intro j lo hi
    obtain row := rows (j-1) (by omega_using [hi])
    simpa only [lookupEntryOffset,Nat.sub_add_cancel lo] using row
  obtain digit := window_affine_repA law m table k 0 yBound entries
  rw [←window_affine_at_eq] at digit
  exact finish_sum_rep law ha offset hP b current digit

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

 structure NativeConstants (base : Addr) (g : Reg → BitVec 64) (V : Prop) [Decidable V] (out : Addr) (s : State) : Prop where
  b : wordsVal s.mem base 568 9<fieldPrime
  one : wordsVal s.mem base 352 9=1
  modulus : ModOkA config.MP' 8192 config.C.p s.mem base
  order : wordsVal s.mem base 136 9=config.C.n
  saved : Spill.Saved base g Cfg.saved s.mem
  flag : word s.mem base 3232=mask V
  outReg : s.gpr .x20=out
  outFit : out.toNat+66≤2^64
  outW : (⟨out,66⟩ : Region)∈s.wr
  outApart : Region.Disjoint ⟨out,66⟩ ⟨base,8192⟩

 theorem native_low_word {base : Addr} {m m' : Mem}
    (low : ∀d,d<856 → m' (off base d)=m (off base d)) {d : Nat} (hd : d+8≤856) :
    word m' base d=word m base d := by
  apply Mem.readW_congr
  intro i hi
  change m' (off base d+BitVec.ofNat 64 i)=m (off base d+BitVec.ofNat 64 i)
  rw [VG.Offset.add_ofNat_add_ofNat]
  exact low _ (by omega_arith)

 theorem native_low_words {base : Addr} {m m' : Mem}
    (low : ∀d,d<856 → m' (off base d)=m (off base d)) {d k : Nat} (hd : d+8*k≤856) :
    wordsVal m' base d k=wordsVal m base d k := by
  apply wordsVal_of_words₂
  intro j hj
  exact native_low_word low (by omega_arith)

 theorem NativeConstants.of_low {base out : Addr} {g : Reg → BitVec 64} {V : Prop} [Decidable V] {s t : State}
    (h : NativeConstants base g V out s) (low : ∀d,d<856 → t.mem (off base d)=s.mem (off base d))
    (flag : word t.mem base 3232=word s.mem base 3232) (outReg : t.gpr .x20=s.gpr .x20) (wr : t.wr=s.wr) :
    NativeConstants base g V out t := by
  refine ⟨?_,?_,?_,?_,?_,flag.trans h.flag,outReg.trans h.outReg,h.outFit,wr.symm ▸ h.outW,h.outApart⟩
  · rw [native_low_words low (by decide)]; exact h.b
  · rw [native_low_words low (by decide)]; exact h.one
  · refine {h.modulus with val:=?_}
    change wordsVal t.mem base 64 9=config.C.p
    rw [native_low_words low (by decide)]
    exact h.modulus.val
  · rw [native_low_words low (by decide)]; exact h.order
  · intro p hp
    change word t.mem base p.2=g p.1
    rw [native_low_word low (by have e:=saved_lt p hp; omega_arith)]
    exact h.saved p hp

 theorem NativeConstants.finish_pre {base table out : Addr} {g : Reg → BitVec 64} {V : Prop} [Decidable V]
    {s t : State} {k : Nat} (h : NativeConstants base g V out s) (post : NativeAfterWindow base table k s t)
    (tableApart : TableWorkspaceApart base table 8192) : FinishPre t table k g V out := by
  obtain c := h.of_low post.lowMemory post.flag post.outputPointer post.wr
  obtain ws : Scr t (t.gpr .x0) 8192 := by rw [post.workspace]; exact post.data.scr
  refine {
    workspace:=ws
    point:=by rw [post.workspace]; exact post.point
    counter:=post.counter
    zero:=by rw [post.workspace]; exact post.data.zero
    b:=by rw [post.workspace]; exact c.b
    oneBound:=by rw [post.workspace,c.one]; decide +kernel
    fieldOne:=by decide +kernel
    tableApart:=by rw [post.workspace]; exact tableApart
    tableRead:=post.data.readable
    tableCanonical:=post.data.canonical
    bits:=by rw [post.workspace]; exact post.data.bits
    modulus:=by rw [post.workspace]; exact c.modulus
    order:=by rw [post.workspace]; exact c.order
    saved:=by rw [post.workspace]; exact c.saved
    flag:=by rw [post.workspace]; exact c.flag
    outReg:=c.outReg
    outFit:=c.outFit
    outW:=c.outW
    outApart:=by rw [post.workspace]; exact c.outApart }

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config windowLoop finishAndWrite)

 def nativeContinuation : Prog isa := .seq windowLoop finishAndWrite

 theorem native_continuation_ok (hc : BaseCfgOk config) {s : State} {base table out : Addr} {k : Nat}
    {g : Reg → BitVec 64} {V : Prop} [Decidable V]
    (data : WindowData base table k s) (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (tableApart : TableWorkspaceApart base table 8192)
    (bound : canonicalPoint s.mem base 1072) (counter : s.gpr .x19=105#64)
    (constants : NativeConstants base g V out s) :
    WP isa nativeContinuation s fun t => ∃mid xv,
      NativeAfterWindow base table k s mid ∧ xv<fieldPrime ∧
      Fin.ofNat fieldPrime xv=(finishSum mid.mem base table k).1*(finishSum mid.mem base table k).2.2^(fieldPrime-2) ∧
      VG.Spec.Ecdsa.bytesAt t.mem out 66=(if finishFullAccept mid table k V then VG.Spec.Weierstrass.toBytes 66 xv else List.replicate 66 0) ∧
      (t.gpr .x0).setWidth 32=(if finishFullAccept mid table k V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [nativeContinuation,WP.seq_iff]
  refine WP.mono (native_window_ok data apart bound counter) fun mid post => ?_
  obtain pre := constants.finish_pre post tableApart
  obtain c := constants.of_low post.lowMemory post.flag post.outputPointer post.wr
  obtain one : wordsVal mid.mem (mid.gpr .x0) 352 9=1 := by rw [post.workspace]; exact c.one
  refine WP.mono (finish_ok_one hc pre one) fun t ⟨x,b,value,bytes,ret,saved,rd,wr,sp,g27,g28,v31⟩ => ?_
  rw [post.workspace] at value
  exact ⟨mid,x,post,b,value,bytes,ret,saved,rd.trans post.rd,wr.trans post.wr,sp.trans post.sp,
    g27.trans (post.tailGP .x27 (by decide)),g28.trans (post.tailGP .x28 (by decide)),v31.trans post.vector31⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass

 def nativeBodyPhases : Prog isa := .seq nativeFront nativeContinuation

 theorem native_body_phases_wp {s : State} {Q : State → Prop} (h : WP isa nativeBodyPhases s Q) :
    WP isa body s Q := by
  simp only [nativeBodyPhases,nativeFront,nativeRecodeArithmetic,nativeFrontArithmetic,nativeContinuation,
    body,sequence,List.foldr_cons,List.foldr_nil,VG.WP.seq_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)] at h ⊢
  exact h

 theorem native_body_continue (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) {s : State} (pre : PrepareStackPre s)
    {Q : State → Prop} (next : ∀front,NativeApiFrontPost s front → WP isa nativeContinuation front Q) :
    WP isa body (allocated 3456 s) Q := by
  apply native_body_phases_wp
  rw [nativeBodyPhases,WP.seq_iff]
  exact WP.mono (native_front_api_ok hc law ha order orderBound pre) next

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64

 structure NativeBodyPre (s : State) : Prop where
  stack : PrepareStackPre s
  outFit : (s.gpr .x0).toNat+66≤2^64
  outW : (⟨s.gpr .x0,66⟩ : Region)∈s.wr
  outApart : Region.Disjoint ⟨s.gpr .x0,66⟩ ⟨s.gpr .x3,8192⟩

 theorem native_body_pre {s : State}
    (h : (VG.Spec.Ecdh.Instance.exchangeContract VG.Spec.EcKey.P521.inst abi 3456).pre s) : NativeBodyPre s := by
  obtain stack := prepare_stack_pre h
  sig_pre [VG.Spec.Ecdh.Instance.exchangeContract,VG.Spec.Ecdh.Instance.exchangeSig,
    VG.Spec.EcKey.P521.inst,VG.Spec.P521.curve,VG.Spec.EcKey.scratchWords,VG.AArch64.abi,VG.AArch64.argRegs] at h
  obtain ⟨_,_,wr,_,_,apart,_,_,_,_,_,_,outFit,_,_,_⟩ := h
  exact ⟨stack,outFit,by rw [wr]; simp,apart⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)
open VG.Proof.Ed25519.AArch64 (Keeps)

 theorem native_ready_constants (hc : BaseCfgOk config) {s args loaded ready : State}
    (pre : NativeBodyPre s) (keep : Keeps [.x2,.x3,.x4,.x6,.x26] (allocated 3456 s) args)
    (stage : St₁ config none args (s.gpr .x3) loaded)
    (core : PrepareCorePost args loaded (s.gpr .x3) (s.gpr .x2) ready)
    {V : Prop} [Decidable V] (flag : word ready.mem (s.gpr .x3) 3232=mask V) :
    NativeConstants (s.gpr .x3) args.gpr V (s.gpr .x0) ready := by
  obtain ⟨_,_,_,_,_,_,_,_,one,modulus,order,saved⟩ := prepare_selected_ready hc stage core
  obtain ⟨_,_,_,_,fields,_,_,_,_,_,g20,_,_,_,_,_,wr,_⟩ := core
  obtain outReg : ready.gpr .x20=s.gpr .x0 :=
    g20.trans (stage.x20.trans (keep.gpr .x0 (by decide)))
  obtain outW : (⟨s.gpr .x0,66⟩ : Region)∈ready.wr := by
    rw [wr,stage.wr,keep.wr]
    exact List.mem_cons_of_mem _ pre.outW
  exact ⟨(fields 568 (by decide)).1,one,modulus,order,saved,flag,outReg,pre.outFit,outW,pre.outApart⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config body)
open VG.Proof.Ed25519.AArch64 (Keeps)

 def NativeBodyRawPost (s t : State) : Prop :=
  ∃ready, ∃ P : Point config.C, ∃front mid xv x y,
    ofBytes (((nativePeerBytes s).drop 1).take config.C.len)=x ∧
    ofBytes ((nativePeerBytes s).drop (config.C.len+1))=y ∧
    (∀h : VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y,P=.affine ⟨x,h.2.1⟩ ⟨y,h.2.2.1⟩) ∧
    onCurve config.C P=true ∧ P≠.infinity ∧ wordsVal ready.mem (s.gpr .x3) 3944 10<32^105 ∧
    wordsVal ready.mem (s.gpr .x3) 3944 10=nativeScalar s%2^521+recodeOffset ∧
    NativeArithmeticPost config.C (s.gpr .x3) (s.sp-3456#64) P (wordsVal ready.mem (s.gpr .x3) 3944 10) ready front ∧
    NativeAfterWindow (s.gpr .x3) (s.sp-3456#64) (wordsVal ready.mem (s.gpr .x3) 3944 10) front mid ∧
    wordsVal mid.mem (s.gpr .x3) 2368 9=nativeScalar s ∧
    Fin.ofNat config.C.p (wordsVal mid.mem (s.gpr .x3) 568 9)=Fin.ofNat config.C.p config.C.b ∧
    xv<fieldPrime ∧ Fin.ofNat fieldPrime xv=
      (finishSum mid.mem (s.gpr .x3) (s.sp-3456#64) (wordsVal ready.mem (s.gpr .x3) 3944 10)).1*
      (finishSum mid.mem (s.gpr .x3) (s.sp-3456#64) (wordsVal ready.mem (s.gpr .x3) 3944 10)).2.2^(fieldPrime-2) ∧
    VG.Spec.Ecdsa.bytesAt t.mem (s.gpr .x0) 66=(if finishFullAccept mid (s.sp-3456#64)
      (wordsVal ready.mem (s.gpr .x3) 3944 10) (VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y)
      then VG.Spec.Weierstrass.toBytes 66 xv else List.replicate 66 0) ∧
    (t.gpr .x0).setWidth 32=(if finishFullAccept mid (s.sp-3456#64)
      (wordsVal ready.mem (s.gpr .x3) 3944 10) (VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y) then 1 else 0) ∧
    (∀r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧
    t.rd=(allocated 3456 s).rd ∧ t.wr=(allocated 3456 s).wr ∧ t.sp=(allocated 3456 s).sp ∧
    t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31

 theorem native_body_raw_ok (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) {s : State} (pre : NativeBodyPre s) :
    WP isa body (allocated 3456 s) (NativeBodyRawPost s) := by
  apply native_body_continue hc law ha order orderBound pre.stack
  intro front frontPost
  obtain ⟨args,loaded,ready,P,keep,stage,core,hP,pne,kbound,arith,outPointer,
    spFront,v31Front,g27Front,g28Front,rdFront,wrFront,_,privateArg,peerPlus,selected⟩ := frontPost
  obtain ⟨x,y,parsedX,parsedY,flagReady,selectedP,originalD,offset⟩ :=
    native_api_decode pre.stack keep stage core privateArg peerPlus selected
  obtain constantsReady := native_ready_constants hc pre keep stage core flagReady
  obtain constants := constantsReady.of_low arith.lowMemory arith.flag arith.outputPointer arith.wr
  obtain bound : canonicalPoint front.mem (s.gpr .x3) 1072 := by
    change wordsVal front.mem (s.gpr .x3) 1072 9<_ ∧ wordsVal front.mem (s.gpr .x3) 1144 9<_ ∧ wordsVal front.mem (s.gpr .x3) 1216 9<_
    rw [arith.accumulatorX,arith.accumulatorY,arith.accumulatorZ]
    obtain hp : config.C.p=fieldPrime := by
      dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,VG.Spec.P521.curve,VG.Spec.P521.p,fieldPrime]
    have hge := hc.p_ge
    rw [hp] at hge
    omega_arith
  refine WP.mono (native_continuation_ok hc arith.data pre.stack.table_scratch.symm pre.stack.tableApart bound
    arith.counter constants) fun t ⟨mid,xv,window,xb,value,bytes,ret,saved,rd,wr,sp,g27,g28,v31⟩ => ?_
  obtain dMid : wordsVal mid.mem (s.gpr .x3) 2368 9=nativeScalar s :=
    window.originalD.trans (arith.originalD.trans originalD)
  obtain bMid : Fin.ofNat config.C.p (wordsVal mid.mem (s.gpr .x3) 568 9)=Fin.ofNat config.C.p config.C.b := by
    rw [native_low_words window.lowMemory (by decide),native_low_words arith.lowMemory (by decide)]
    exact prepare_selected_b hc core
  refine ⟨ready,P,front,mid,xv,x,y,parsedX,parsedY,selectedP,hP,pne,kbound,offset,
    arith,window,dMid,bMid,xb,value,bytes,ret,?_,rd.trans rdFront,wr.trans wrFront,sp.trans spFront,
    g27.trans g27Front,g28.trans g28Front,v31.trans v31Front⟩
  intro r hr
  obtain fresh : ∀r∈Cfg.saved.map Prod.fst,r∉[Reg.x2,Reg.x3,Reg.x4,Reg.x6,Reg.x26] := by decide
  exact (saved r hr).trans (keep.gpr r (fresh r hr))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (windowLoop)

 theorem window_initial_group {C : Curve} {m : Mem} {base : Addr} {k : Nat} {P : Point C}
    (zero : wordsVal m base 1216 9=0) (below : k+16*Window5.geom 105<32^105) :
    InvJ C (pointAt C m base 1072).1 (pointAt C m base 1072).2.1
      (pointAt C m base 1072).2.2 (mul (Window5.winE (k+16*Window5.geom 105) 105 105) P) := by
  rw [Window5.winE_top below,Window5.mul_zero_pt]
  refine Or.inl ⟨rfl,?_⟩
  change Fin.ofNat C.p (wordsVal m base 1216 9)=0
  rw [zero]
  rfl

 theorem window_loop_group_ok {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C) (order : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (nonzero : P≠.infinity) (hn : 64≤C.n)
    {s : State} {base table : Addr} {k : Nat} (hk : k<C.n)
    (data : WindowData base table (k+16*Window5.geom 105) s)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (bound : canonicalPoint s.mem base 1072) (counter : s.gpr .x19=105#64)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal s.mem table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal s.mem table (lookupEntryOffset d+72) 9)) 1 (mul d P))
    (current : InvJ C (pointAt C s.mem base 1072).1 (pointAt C s.mem base 1072).2.1
      (pointAt C s.mem base 1072).2.2 (mul (Window5.winE (k+16*Window5.geom 105) 105 105) P)) :
    WP isa windowLoop s fun t =>
      canonicalPoint t.mem base 1072 ∧
      InvJ C (pointAt C t.mem base 1072).1 (pointAt C t.mem base 1072).2.1
        (pointAt C t.mem base 1072).2.2 (mul (Window5.winE (k+16*Window5.geom 105) 105 1) P) ∧
      WindowData base table (k+16*Window5.geom 105) t ∧ WindowPhaseFrame base s.mem t.mem ∧ WindowStepPublic s t ∧
      t.gpr .x19=1#64 ∧ t.gpr .x4=0#64 := by
  refine WP.mono (window_loop_104 data apart bound counter) fun t ⟨b,p,d,f,pub,c19,c4⟩ => ?_
  rw [window_run_generic] at p
  obtain canonical : ∀d,1≤d → d≤16 → wordsVal s.mem table (lookupEntryOffset d+72) 9<C.p := by
    intro d h1 hd
    rw [hp]
    exact (data.canonical d h1 hd).2
  obtain group := window_run_group_transfer (steps:=104) hp law ha order hP nonzero hn hk (by decide)
    s.mem table p canonical entries current
  exact ⟨b,group,d,f,pub,c19,c4⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64

private theorem native_prime : config.C.p=fieldPrime := by
  dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,Spec.P521.curve,Spec.P521.p,fieldPrime]

private def outputResult (r : Option (List Byte)) (ret : BitVec 32) (bytes : List Byte) (n : Nat) : Prop :=
  match r with
  | some result => ret=1 ∧ bytes=result
  | none => ret=0 ∧ bytes=List.replicate n 0

private theorem output_post {r : Option (List Byte)} {z bytes : List Byte} {ret : BitVec 32}
    {Q : Prop} [Decidable Q] {n : Nat}
    (spec : r=if Q then some z else none)
    (hb : bytes=if decide Q then z else List.replicate n 0)
    (hr : ret=if decide Q then 1 else 0) :
    outputResult r ret bytes n := by
  rw [spec]
  by_cases h : Q
  · simp only [h,ite_true,decide_true,outputResult] at hb hr ⊢
    exact ⟨hr,hb⟩
  · simp only [h,ite_false,decide_false,Bool.false_eq_true,outputResult] at hb hr ⊢
    exact ⟨hr,hb⟩

 theorem native_body_correctness (_hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) {s t : State} (pre : PrepareStackPre s)
    (raw : NativeBodyRawPost s t) : EPost config s t := by
  obtain ⟨ready,P,front,mid,xv,x,y,parseX,parseY,selected,hP,pne,kbound,offset,arith,window,
    original,b,xb,value,bytes,ret,saved,rd,wr,sp,g27,g28,v31⟩ := raw
  let d := nativeScalar s
  let k := wordsVal ready.mem (s.gpr .x3) 3944 10
  obtain hn : 64≤config.C.n := by decide +kernel
  obtain orderSize : config.C.n≤2^521 := by decide +kernel
  have goodOffset (hd : d<config.C.n) : k=d+16*Window5.geom 105 := by
    obtain below : d<2^521 := Nat.lt_of_lt_of_le hd orderSize
    change k=d+recodeOffset
    exact offset.trans (congrArg (fun z => z+recodeOffset) (Nat.mod_eq_of_lt below))
  obtain canonical : ∀j,1≤j → j≤16 → wordsVal front.mem (s.sp-3456#64) (lookupEntryOffset j+72) 9<config.C.p := by
    intro j lo hi
    rw [native_prime]
    exact (arith.data.canonical j lo hi).2
  obtain entries : ∀j,1≤j → j≤16 → Rep config.C (Fin.ofNat config.C.p (wordsVal front.mem (s.sp-3456#64) (lookupEntryOffset j) 9))
      (Fin.ofNat config.C.p (wordsVal front.mem (s.sp-3456#64) (lookupEntryOffset j+72) 9)) 1 (mul j P) := by
    intro j lo hi
    obtain row := (arith.affine (j-1) (by omega_using [hi])).1
    simpa only [lookupEntryOffset,Nat.sub_add_cancel lo] using row
  have current (hd : d<config.C.n) : InvJ config.C (pointAt config.C mid.mem (s.gpr .x3) 1072).1
      (pointAt config.C mid.mem (s.gpr .x3) 1072).2.1 (pointAt config.C mid.mem (s.gpr .x3) 1072).2.2
      (mul (Window5.winE k 105 1) P) := by
    obtain initial := window_initial_group (C:=config.C) (P:=P) arith.accumulatorZ (show d+16*Window5.geom 105<32^105 by rw [←goodOffset hd]; exact kbound)
    have p := window.value
    rw [window_run_generic] at p
    change ordinaryPoint mid.mem (s.gpr .x3) 1072=windowNonfinalF (fun j => windowAffineN fieldPrime front.mem (s.sp-3456#64) k j) 104 (ordinaryPoint front.mem (s.gpr .x3) 1072) at p
    rw [goodOffset hd] at p ⊢
    exact window_run_group_transfer native_prime law ha order hP pne hn hd (by decide) front.mem (s.sp-3456#64)
      p canonical entries initial
  obtain rows : ∀i,i<16 → Rep config.C (Fin.ofNat config.C.p (wordsVal mid.mem (s.sp-3456#64) (216*i) 9))
      (Fin.ofNat config.C.p (wordsVal mid.mem (s.sp-3456#64) (216*i+72) 9)) 1 (mul (i+1) P) := by
    intro i hi
    rw [WindowPhaseFrame.table window.frame pre.table_scratch.symm _ (by omega_using [hi]),
      WindowPhaseFrame.table window.frame pre.table_scratch.symm _ (by omega_using [hi])]
    exact (arith.affine i hi).1
  have result (hd : d<config.C.n) : Rep config.C (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).1
      (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).2.1
      (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).2.2 (mul d P) :=
    finish_sum_table_rep native_prime law ha (goodOffset hd) hP b (current hd) window.data.canonical rows
  obtain val := finish_value_transfer native_prime value
  obtain bound : xv<config.C.p := by rw [native_prime]; exact xb
  obtain spec := VG.Proof.Ecdh.exchange_eq_of_lt law
    (bs:=nativePeerBytes s) (by rw [length_bytesAt]; rfl)
    (b0:=s.mem (s.gpr .x2)) (by
      change (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1+2*config.C.len)).head?=_
      rw [peer_bytes]; rfl) parseX parseY selected result bound val
  obtain accept : finishFullAccept mid (s.sp-3456#64) k (VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y)=
      decide ((1≤d ∧ d<config.C.n) ∧ VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y ∧ (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).2.2≠0) := by
    unfold finishFullAccept
    rw [window.workspace,original]
    rw [decide_eq_decide]
    obtain nz := not_congr (finish_zero_transfer native_prime mid.mem (s.gpr .x3) (s.sp-3456#64) k)
    constructor
    · rintro ⟨⟨v,lo,hi⟩,z⟩; exact ⟨⟨lo,hi⟩,v,nz.mp z⟩
    · rintro ⟨⟨lo,hi⟩,v,z⟩; exact ⟨⟨v,lo,hi⟩,nz.mpr z⟩
  change (match Spec.Ecdh.exchange config.C d (nativePeerBytes s) with
    | some z => (t.gpr .x0).setWidth 32=1 ∧ Spec.Ecdsa.bytesAt t.mem (s.gpr .x0) 66=z
    | none => (t.gpr .x0).setWidth 32=0 ∧ Spec.Ecdsa.bytesAt t.mem (s.gpr .x0) 66=List.replicate 66 0)
  change Spec.Ecdh.exchange config.C d (nativePeerBytes s) =
    if (1≤d ∧ d<config.C.n) ∧ VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y ∧
      (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).2.2≠0
    then some (toBytes 66 xv) else none at spec
  rw [accept] at bytes ret
  exact output_post spec bytes ret

end VG.Proof.Weierstrass.AArch64.P521Native

end

end


@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Weierstrass
open VG.Impl.Weierstrass.AArch64.P521Native (config body)

 theorem native_body_api_ok (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) {s : State}
    (pre : (VG.Spec.Ecdh.Instance.exchangeContract VG.Spec.EcKey.P521.inst abi 3456).pre s) :
    WP isa body (allocated 3456 s) fun t =>
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VG.Proof.Ecdh.AArch64.EPost config s t ∧
      t.rd=(allocated 3456 s).rd ∧ t.wr=(allocated 3456 s).wr ∧ t.sp=(allocated 3456 s).sp ∧
      t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  obtain bodyPre := native_body_pre pre
  obtain orderBound : 17≤config.C.n := by decide +kernel
  refine WP.mono (native_body_raw_ok hc law ha order orderBound bodyPre) fun t raw => ?_
  obtain correct := native_body_correctness hc law ha order bodyPre.stack raw
  obtain ⟨ready,P,front,mid,xv,x,y,parseX,parseY,selected,hP,pne,kbound,offset,arith,window,
    original,b,xb,value,bytes,ret,saved,rd,wr,sp,g27,g28,v31⟩ := raw
  exact ⟨saved,correct,rd,wr,sp,g27,g28,v31⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdh.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config body exchange outerBlock000 outerBlock172)

private theorem epost_keep {c : Cfg} {s t v : State} (h : EPost c s t)
    (mem : v.mem=t.mem) (reg : v.gpr .x0=t.gpr .x0) : EPost c s v := by
  unfold EPost at h ⊢
  rw [mem,reg]
  exact h

 theorem native_exchange_api_ok (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) {s : State} (pre : nativeContract.pre s) :
    WP isa exchange s fun t => EPost config s t ∧
      (∀r∈[Reg.x19,Reg.x20,Reg.x21,Reg.x22,Reg.x23,Reg.x24,Reg.x25,Reg.x26,Reg.x27,Reg.x28,Reg.x30],t.gpr r=s.gpr r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  obtain entry := native_pre_saved pre
  obtain stack := prepare_stack_pre entry
  change WP isa (.seq (.block outerBlock000) (.seq (.frame (.alloc 3456) body (.free 3456)) (.seq (.block outerBlock172) (.block [])))) s _
  apply WP.seq
  refine WP.mono (native_prologue_ok s) fun u hu => ?_
  subst u
  apply WP.seq
  apply WP.alloc (by decide) stack.room
  refine WP.mono (native_body_api_ok hc law ha order entry) fun t ⟨saved,api,rd,wr,sp,g27,g28,v31⟩ => ?_
  apply WP.seq
  refine WP.mono (native_epilogue_ok (freed 3456 t)) fun v hv => ?_
  obtain ⟨g26,keep,_⟩ := hv
  apply WP.block_nil
  have reg r (hr : r≠Reg.x26) : v.gpr r=t.gpr r := keep.gpr r (by simpa using hr)
  refine ⟨?_,?_,?_,?_,?_⟩
  · change EPost config s v
    change EPost config s t at api
    obtain mem : v.mem=t.mem := by simpa only [freed] using keep.mem
    exact epost_keep api mem (reg .x0 (by decide))
  · intro r hr
    by_cases eq26 : r=Reg.x26
    · subst r
      rw [g26]
      change (t.v .v31).extractLsb' 64 64=s.gpr .x26
      rw [v31,native_saved_high]
    · rw [reg r eq26]
      obtain cases : r∈Cfg.saved.map Prod.fst ∨ r=Reg.x27 ∨ r=Reg.x28 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false,Cfg.saved,List.map_cons,List.map_nil] at hr ⊢
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|bad|rfl|rfl|rfl <;> simp_all
      rcases cases with h|rfl|rfl
      · exact saved r h
      · exact g27
      · exact g28
  · have vr : v.rd=t.rd := by simpa only [freed] using keep.rd
    have tr : t.rd=s.rd := rd
    exact vr.trans tr
  · change v.wr=s.wr
    rw [keep.wr]
    change t.wr.tail=s.wr
    rw [wr]
    rfl
  · rw [keep.sp]
    change t.sp+3456#64=s.sp
    rw [sp]
    exact BitVec.sub_add_cancel _ _

end VG.Proof.Weierstrass.AArch64.P521Native
