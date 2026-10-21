module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeFn
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangePre
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! Exchange reserves the outer frame plus the callable arithmetic stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm

theorem pre128 (s : State) (pre : (Spec.Ffdh.exchangeContract abi 176).pre s) :
    (Spec.Ffdh.exchangeContract abi 128).pre s := by
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre ⊢
  obtain ⟨stackFit, argFit, rd, wr, outDom, outX, outY, outS, outArgs, domS, xS, yS, sArgs,
    stackOut, stackDom, stackX, stackY, stackS, stackArgs, outFit, domFit, xFit, yFit, sFit,
    bounds, domainLen, outLen, yLen, xPositive, xMax, space⟩ := pre
  have inner : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 128, 128⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 176, 176⟩ :=
    Offset.below_mono _ (by decide) (by decide)
  exact ⟨by omega, argFit, rd, wr, outDom, outX, outY, outS, outArgs, domS, xS, yS, sArgs,
    stackOut.sub_left inner, stackDom.sub_left inner, stackX.sub_left inner,
    stackY.sub_left inner, stackS.sub_left inner, stackArgs.sub_left inner,
    outFit, domFit, xFit, yFit, sFit, bounds, domainLen, outLen, yLen, xPositive, xMax, space⟩

theorem input (s : State) (pre : (Spec.Ffdh.exchangeContract abi 176).pre s)
    {p : Inputs} {yb xb : List Byte}
    (base : stackArg s 5 = p.base) (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (peer : stackArg s 3 = p.publicValue) (scalar : stackArg s 1 = p.privateValue)
    (count : (stackArg s 0).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom)
    (peerBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    FnInput p yb xb s := by
  have old := exchange_input s (pre128 s pre) base out domain peer scalar count capacity privateCount domainBytes peerBytes scalarBytes
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, _, _, _, _, _, _, _, _, _, _, _, stackOut, stackDom, stackX, stackY, stackS,
    _, _, _, _, _, _, _, _, outLen, yLen, _, _, _⟩ := pre
  have domLen : (s.gpr .r3).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have xLen : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [outLen,count,out] at stackOut
  rw [yLen,count,peer] at stackY
  rw [privateCount,scalar] at stackX
  rw [domain,domLen] at stackDom
  rw [base,capacity,Nat.mul_comm p.len 8] at stackS
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackOut stackDom stackX stackY stackS
  have calls := CallMemory.of_outer (p := p) (n := xb.length) stackFit (entered_sp s)
    stackS stackDom.symm stackY.symm (by rw [xLen]; exact stackX.symm) stackOut.symm
  refine ⟨old,calls,?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact old.saved r hr
  · have eq := List.mem_singleton.mp hr
    subst r
    have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
    have fit : (entered s).sp.toNat + 72 < 2^32 := by
      rw [entered_nat s (by omega)]; have := s.sp.isLt; omega
    rw [shifted,VG.Arm.addr_add fit,belowA,addr_sub' calls.stack.fit]
    exact (Offset.disjoint_below_above _ (m:=48) (a:=72) (l:=56) (by decide)).symm

end VG.Proof.Ffdh.Arm.SharedExchange
