module

-- separate module: the complete final-window machine contract is independent of the outer-loop composition and group/API interpretation

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFront
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFinal
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAssemble
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.Block

/-! Standalone full final-window contract, preserving every checked input path. -/

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
