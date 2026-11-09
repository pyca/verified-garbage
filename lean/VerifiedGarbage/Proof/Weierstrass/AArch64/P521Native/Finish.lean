module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishInverse
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProducts
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrames
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationMath
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishChecks
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFront
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAssemble

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
  have hu := hs.of_keepRegs ku (by decide)
  have Mu : ModOkA config.MP' 8192 config.C.p u.mem base := {hM with val:=by rw [uc.wordsVal (by decide) (by decide)]; exact hM.val}
  have bu : wordsVal u.mem base 1216 9<fieldPrime := by rw [zu]; exact bounds 1432 (by simp)
  rw [WP.seq_iff]
  refine WP.mono (finish_inverse_phase_ok hc hu Mu bu)
    fun v ⟨invBound,invValue,uv,zero,rd,wr,sp,g20,g26,g30,v31,converted,gExtra⟩ => ?_
  have hv : Scr v base 8192 := ⟨zero,by rw [wr]; exact hu.wr,hu.nowrap,hu.enc⟩
  have xSame : wordsVal v.mem base 1072 9=wordsVal s.mem base 1288 9 := by
    rw [uv.wordsVal (by decide) (by decide),xu]
  have oneSame : wordsVal v.mem base 352 9=wordsVal s.mem base 352 9 := by
    rw [uv.wordsVal (by decide) (by decide),uc.wordsVal (by decide) (by decide)]
  let E : Nat → Fin fieldPrime := fun d => Fin.ofNat fieldPrime (wordsVal v.mem base d 9)
  have live : OrdinaryInv base fieldPrime id [1072,2152,352] E (fun _ => 1) v := by
    constructor
    · intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl
      · simpa only [id_eq,Nat.one_mul,xSame] using bounds 1288 (by simp)
      · simpa only [id_eq,Nat.one_mul] using invBound
      · simpa only [id_eq,Nat.one_mul,oneSame] using bounds 352 (by simp)
    · intro d _; rfl
  refine WP.mono (finish_products_machine_ok hv live) fun t ⟨it,ht,kt,ft⟩ => ?_
  have productsU := field_program_frame_unch ft
  have allU : Unch base finalizeWrites s.mem t.mem := uc.trans (uv.trans productsU)
  have outBound := it.bound 2584 (by decide)
  have outValue := it.value 2584 (by decide)
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
  have mnu : wordsVal u.mem base 136 9=config.C.n := by
    rw [frame.wordsVal (by decide) (by decide)]; exact mn
  have savedU := Saved.unch saved (W:=finalizeWrites) (by decide) frame
  have flagU : word u.mem base 3232=mask V := by
    rw [frame.word (by decide) (by decide)]; exact flag
  have outU : u.gpr .x20=out := g20.trans outReg
  have wrU : (⟨out,66⟩ : Region)∈u.wr := by rw [wr]; exact outW
  have dSame : wordsVal u.mem base 2368 9=wordsVal s.mem base 2368 9 := frame.wordsVal (by decide) (by decide)
  have accept : VG.Proof.Ecdh.AArch64.ok config base u V=finishAccept base s V := by
    simp only [VG.Proof.Ecdh.AArch64.ok,sv,finishAccept,
      (show config.n=9 from rfl),(show config.sl D=2368 from rfl),(show config.sl RZ=1216 from rfl)]
    rw [dSame,converted]
    simp only [ne_eq,toMontValue_zero_iff (bounds 1432 (by simp))]
  obtain ⟨trace,t,exec,bytes,ret,restored⟩ := checked_finish_ok hc hu mnu savedU flagU outU outFit wrU outApart
  let code : List Instr := config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++VG.Impl.Ecdh.AArch64.Cfg.finish config
  have check27 : code.all (fun i => decide (clobbers i .x27=false))=true := by lit_decide
  have check28 : code.all (fun i => decide (clobbers i .x28=false))=true := by lit_decide
  have checkV : code.all (fun i => decide (vdstOf i≠some .v31))=true := by lit_decide
  have hc27 : ∀i∈instrs (.block code : Prog isa),clobbers i .x27=false := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using check27
  have hc28 : ∀i∈instrs (.block code : Prog isa),clobbers i .x28=false := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using check28
  have hcV : ∀i∈instrs (.block code : Prog isa),vdstOf i≠some .v31 := by
    simpa only [instrs,List.all_eq_true,decide_eq_true_eq] using checkV
  have regions := Exec.rdwr exec
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
  have Mu : ModOkA config.MP' 8192 config.C.p u.mem (s.gpr .x0) :=
    {pre.modulus with val:=by rw [frame.wordsVal (by decide) (by decide)]; exact pre.modulus.val}
  have oneSame : wordsVal u.mem (s.gpr .x0) 352 9=wordsVal s.mem (s.gpr .x0) 352 9 := frame.wordsVal (by decide) (by decide)
  have bounds : ∀d∈[1288,1360,1432,352],wordsVal u.mem (s.gpr .x0) d 9<fieldPrime := by
    intro d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl
    · exact bu.1
    · exact bu.2.1
    · exact bu.2.2
    · rw [oneSame]; exact pre.oneBound
  have savedU := Saved.unch pre.saved (W:=finishAllFrontWrites) (by decide) frame
  have mnU : wordsVal u.mem (s.gpr .x0) 136 9=config.C.n := by rw [frame.wordsVal (by decide) (by decide)]; exact pre.order
  have flagU : word u.mem (s.gpr .x0) 3232=mask V := by rw [frame.word (by decide) (by decide)]; exact pre.flag
  have outU : u.gpr .x20=out := g20.trans pre.outReg
  have wrU : (⟨out,66⟩ : Region)∈u.wr := by rw [wr]; exact pre.outW
  have dSame : wordsVal u.mem (s.gpr .x0) 2368 9=wordsVal s.mem (s.gpr .x0) 2368 9 := frame.wordsVal (by decide) (by decide)
  have px := congrArg Prod.fst pu
  have pz := congrArg (fun P => P.2.2) pu
  dsimp only [ordinaryPoint] at px pz
  have accept : finishAccept (s.gpr .x0) u V=finishFullAccept s table k V := by
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
  have oneFin : Fin.ofNat fieldPrime (wordsVal s.mem (s.gpr .x0) 352 9)=(1 : Fin fieldPrime) := by
    rw [one]
    exact finite_one
  rw [oneFin,Lean.Grind.Semiring.mul_one] at value
  exact ⟨xv,xb,value,bytes,ret,restore,rd,wr,sp,g27,g28,v31⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end
