module

public import VerifiedGarbage.Proof.Ffdh.Arm.DomainFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! The shared domain signature supplies the complete native frame and buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem domain_input (s : State) (pre : (Spec.Ffdh.checkDomainContract abi 128).pre s)
    {p : Inputs} (base : s.gpr .r3 = p.base) (domain : s.gpr .r0 = p.domain)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 0).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom) :
    DomainFnInput p s := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, rd, wr, domS, _, stackDom, stackS, _, domFit, sFit, _, _, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [domain, domLen] at rd domS stackDom domFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackS
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have domOctets : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domRead, domS, by rw [← domLen]; exact domainBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit stackS, entered_octets domOctets stackFit stackDom,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  refine ⟨stackFit, args, domain, ?_, ?_, base, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

end VG.Proof.Ffdh.Arm
