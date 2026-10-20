module

public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicFn
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target

/-! The shared signature supplies the native public-check frame and buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem checkPublic_input (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 128).pre s)
    {p : Inputs} {yb : List Byte}
    (base : stackArg s 1 = p.base) (domain : s.gpr .r0 = p.domain) (publicValue : s.gpr .r3 = p.publicValue)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 2).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (publicBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb) :
    CheckPublicFnInput p yb s := by
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, sArgs, stackDom, stackY, stackS, stackArgs,
    domFit, yFit, sFit, _, _, yLen, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have length : yb.length = p.k := by
    have eq := congrArg List.length publicBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [yLen, count] at rd yS stackY yFit
  rw [domain] at rd domS stackDom domFit
  rw [publicValue] at rd yS stackY yFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS yS sArgs stackS sFit
  rw [domLen] at rd domS stackDom domFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackY stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have valueRead : InRegions (s.rd ++ s.wr) (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have domOctets : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domRead, domS, by rw [← domLen]; exact domainBytes⟩
  have valueOctets : Octets p.base p.publicValue p.len yb s :=
    ⟨by rw [length]; exact yFit, by rw [length]; exact valueRead,
      by rw [length]; exact yS, by rw [length]; exact publicBytes⟩
  have locals := entered_locals s stackFit stackS
  have domEntered := entered_octets domOctets stackFit stackDom
  have valueEntered := entered_octets valueOctets stackFit (by rw [length]; exact stackY)
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, locals, domEntered,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  have argAddr : stackArgAddr s 1 = off (State.addr s.sp) 4 := VG.Arm.addr_add (by omega)
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have contains : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 1) 4 := by
    rw [argStart, argAddr]
    exact Offset.contains_base _ (by decide) (by decide)
  have argRead : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 4 :=
    ⟨⟨stackArgAddr s 0, 12⟩, List.mem_append_left _ (by rw [rd]; simp), contains⟩
  have nativeRoom : (entered s).sp.toNat + 132 < 2 ^ 32 := by rw [entered_nat s stackFit]; omega
  have nativeAddr : off (State.addr (entered s).sp) 132 = stackArgAddr s 1 := by
    change State.addr (entered s).sp + BitVec.ofNat 64 132 = _
    rw [← VG.Arm.addr_add nativeRoom, entered_sp]
    have split : BitVec.ofNat 32 132 = BitVec.ofNat 32 128 + BitVec.ofNat 32 4 := rfl
    rw [split, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rfl
  have incoming : IncomingScratch p (entered s) := by
    refine ⟨by rw [entered_nat s stackFit]; omega, ?_, ?_⟩
    · rw [nativeAddr]; exact entered_read argRead
    · rw [nativeAddr]
      have word := (entered_frame s stackFit).readW (w := 32) contains (by
        intro r hr
        rw [List.mem_singleton] at hr
        subst r
        exact stackArgs.symm.sub_right (saved_sub_reserved s stackFit)) (by decide)
      rw [word]
      exact base
  refine ⟨stackFit, args, incoming, domain, ?_, ?_, publicValue, valueEntered, length, ?_, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [length]
    exact stackY.symm.sub_right (locals_sub_reserved s stackFit)
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

end VG.Proof.Ffdh.Arm
