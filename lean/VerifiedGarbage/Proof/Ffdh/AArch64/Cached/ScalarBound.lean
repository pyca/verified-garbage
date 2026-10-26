module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BoundHead
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BoundNoQ
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadArray
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! The rejection bound is exactly the reviewed q-or-p−1 value for both domain encodings. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem scalarBound_ok {s : State} {B ptr : Addr} {Z w k dl : Nat} {mi : BitVec 64} {dom : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl) (source : Src s B Z ptr dom)
 (pointer : word s.mem B (8*sDom)=ptr) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (modulus : wv s.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p)
 (odd : (Spec.Ffdh.domainOf k dom).p%2=1) :
 WP isa Generate.bound s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 5) w=Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ∧
 Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Generate.bound
 rw [WP.seq_iff]
 refine WP.mono (boundHead_ok good room size shape pointer length domainLength) ?_
 rintro a ⟨⟨ptrA,lenA,testA,offsetA,memA⟩,restA⟩
 have goodA : Good a B Z w mi :=
  ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,memA ▸ good.hdr⟩
 have sourceA := source.congrK (fun x _ =>by rw [memA]) restA
 by_cases noQ : dl=2*k
 · have branch := boundNoQ_ok goodA room (by rw [words];omega) (by rw [words];omega)
    (by rw [memA,modulus];exact odd)
   have condition : isa.eval (.zero .x .x3) a=some true := by rw [eval_zero,testA,noQ,Nat.sub_self];decide
   obtain ⟨tr,t,run,goodT,value,frame,rest⟩ := branch
   refine ⟨_,t,.iteT condition run,goodT,?_,?_,(restA.trans rest).mono (by simp [mmRegs])⟩
   · rw [memA,modulus] at value
     simpa only [Spec.Ffdh.scalarBound,Spec.Ffdh.domainOf,
      ite_eq_right (by omega : ¬dom.length=3*k),Option.getD_none] using value
   · rw [←memA];exact frame
 · have three : dl=3*k := by omega
   have condition : isa.eval (.zero .x .x3) a=some false := by
    rw [eval_zero,testA,three]
    have nonzero : BitVec.ofNat 64 (3*k-2*k)≠0#64 := by
     intro eq;have := congrArg BitVec.toNat eq;change (3*k-2*k)%2^64=0 at this;omega
    simp [nonzero]
   have body : WP isa (.seq (.block [.add .x .x1 .x1 .x4]) (load 5)) a fun t =>
    Good t B Z w mi ∧ wv t.mem B (slot w 5) w=Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ∧
    Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.x1] (Q:=fun b =>b.gpr .x1=ptr+BitVec.ofNat 64 (2*k) ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
    · brun [ptrA,offsetA]
    · rintro b ⟨⟨ptrB,memB⟩,restB⟩
      have goodB : Good b B Z w mi :=
       ⟨goodA.scr.congr restB.wr,(restB.gpr .x0 (by decide)).trans goodA.x0,memB ▸ goodA.hdr⟩
      have srcB := sourceA.congrK (fun x _ =>by rw [memB]) restB
      refine WP.mono (loadArray_ok goodB room words positive size (by decide : 5<8)
       (src_take (src_drop srcB (2*k)) k) (by simp only [List.length_take,List.length_drop];omega)
       ptrB ((restB.gpr .x2 (by decide)).trans lenA)) ?_
      rintro t ⟨goodT,value,frame,restT⟩
      refine ⟨goodT,?_,?_,((restA.trans restB).trans restT).mono (by simp [mmRegs])⟩
      · simpa only [Spec.Ffdh.scalarBound,Spec.Ffdh.domainOf,ite_eq_left (by omega : dom.length=3*k),Option.getD_some] using value
      · rw [←memA,←memB];exact frame
   obtain ⟨tr,t,run,post⟩ := body
   exact ⟨_,t,.iteF condition run,post⟩

end VG.Proof.Ffdh.AArch64.Cached
