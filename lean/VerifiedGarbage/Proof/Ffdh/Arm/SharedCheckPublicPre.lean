module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicFn
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicPre
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! The public-check signature reserves the outer frame and shared-call stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm

theorem sharedCheckPublic_pre128 (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 176).pre s) :
    (Spec.Ffdh.checkPublicContract abi 128).pre s := by
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre ⊢
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, sArgs, stackDom, stackY, stackS, stackArgs,
    domFit, yFit, sFit, bounds, domainLen, yLen, space⟩ := pre
  have inner : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 128, 128⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 176, 176⟩ :=
    Offset.below_mono _ (by decide) (by decide)
  exact ⟨by omega, argFit, rd, wr, domS, yS, sArgs, stackDom.sub_left inner,
    stackY.sub_left inner, stackS.sub_left inner, stackArgs.sub_left inner,
    domFit, yFit, sFit, bounds, domainLen, yLen, space⟩

theorem sharedCheckPublic_input (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 176).pre s)
    {p : Inputs} {yb : List Byte}
    (base : stackArg s 1 = p.base) (domain : s.gpr .r0 = p.domain) (publicValue : s.gpr .r3 = p.publicValue)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 2).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (publicBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb) :
    SharedCheckPublicFnInput p yb s := by
  have old := checkPublic_input s (sharedCheckPublic_pre128 s pre) base domain publicValue count capacity domainBytes publicBytes
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, _, _, _, _, _, stackDom, stackY, stackS, _, _, _, _, _, _, yLen, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [yLen,count,publicValue] at stackY
  rw [domain,domLen] at stackDom
  rw [base,capacity,Nat.mul_comm p.len 8] at stackS
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackY stackS
  have calls := DomainCallMemory.of_outer stackFit (entered_sp s) stackS stackDom.symm stackY.symm
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

end VG.Proof.Ffdh.Arm
