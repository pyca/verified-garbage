module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptInput
import VerifiedGarbage.Proof.Framework.GetElem

/-! The reviewed public arguments and leakage determine every native timing parameter. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64

theorem attemptFront_congr {s t : State} (gs : AttemptGeometry s) (gt : AttemptGeometry t)
 (x : s.gpr .x0=t.gpr .x0) (y : s.gpr .x2=t.gpr .x2) (dp : s.gpr .x4=t.gpr .x4)
 (dl : s.gpr .x5=t.gpr .x5) (len : s.gpr .x6=t.gpr .x6) (rp : s.gpr .x7=t.gpr .x7)
 (base : stackArg s 1=stackArg t 1) (size : stackArg s 2=stackArg t 2)
 (ctx : stackArg s 3=stackArg t 3) (count : stackArg s 4=stackArg t 4)
 (dom : attemptDomain s=attemptDomain t)
 (status : Spec.Ffdh.keyStatus (attemptParameters s) (attemptScalar s)=Spec.Ffdh.keyStatus (attemptParameters t) (attemptScalar t)) :
 attemptFront s gs=attemptFront t gt :=by
 unfold attemptFront attemptNativeParameters checkedParameters
 simp only [x,y,dp,dl,len,rp,base,size,ctx,count,dom,status]

theorem attemptPub_front {s t : State} (gs : AttemptGeometry s) (gt : AttemptGeometry t) (h : attemptPub s t) :
 attemptFront s gs=attemptFront t gt ∧ s.sp=t.sp :=by
 obtain ⟨regs,sp,stack,leak⟩:=h
 have raw : ∀ r∈argRegs,s.gpr r=t.gpr r :=regs
 have x:=raw .x0 (by decide)
 have y:=raw .x2 (by decide)
 have dp:=raw .x4 (by decide)
 have dl:=raw .x5 (by decide)
 have len:=raw .x6 (by decide)
 have rp:=raw .x7 (by decide)
 rw [stackArgs_five,stackArgs_five] at stack
 have a0:= (List.cons.inj stack).1
 have st1:=(List.cons.inj stack).2
 have a1:=(List.cons.inj st1).1
 have st2:=(List.cons.inj st1).2
 have a2:=(List.cons.inj st2).1
 have st3:=(List.cons.inj st2).2
 have a3:=(List.cons.inj st3).1
 have a4:=(List.cons.inj (List.cons.inj st3).2).1
 have parts:=List.append_inj leak (by
  simp only [List.length_map,attemptDomain,Spec.Rsa.bytesAt,List.length_range,dl])
 have dom : attemptDomain s=attemptDomain t :=by
  have recover:=congrArg (List.map (BitVec.ofNat 8)) parts.1
  simpa only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id'] using recover
 exact ⟨attemptFront_congr gs gt x y dp dl len rp a1 a2 a3 a4 dom (List.cons.inj parts.2).1,sp⟩

end VG.Proof.Ffdh.AArch64.Cached
