module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFn
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target

/-! The shared exchange signature supplies its native buffers and incoming argument words. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem exchange_input (s : State) (pre : (Spec.Ffdh.exchangeContract abi 128).pre s)
    {p : Inputs} {yb xb : List Byte}
    (base : stackArg s 5 = p.base) (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (peer : stackArg s 3 = p.publicValue) (scalar : stackArg s 1 = p.privateValue)
    (count : (stackArg s 0).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom)
    (peerBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    ExchangeFnInput p yb xb s := by
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, outDom, outX, outY, outS, outArgs, domS, xS, yS, sArgs,
    stackOut, stackDom, stackX, stackY, stackS, stackArgs, outFit, domFit, xFit, yFit, sFit,
    _, _, outLen, yLen, xPositive, xMax, _⟩ := pre
  have domLen : (s.gpr .r3).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have yLength : yb.length = p.k := by
    have eq := congrArg List.length peerBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [count] at outLen yLen xMax
  rw [outLen] at wr outDom outX outY outS outArgs stackOut outFit
  rw [yLen] at rd outY yS stackY yFit
  rw [privateCount] at rd outX xS stackX xFit xPositive xMax
  rw [out] at wr outDom outX outY outS outArgs stackOut outFit
  rw [domain, domLen] at rd outDom domS stackDom domFit
  rw [peer] at rd outY yS stackY yFit
  rw [scalar] at rd outX xS stackX xFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr outS domS xS yS sArgs stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackOut stackDom stackX stackY stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domainRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have peerRead : InRegions (s.rd ++ s.wr) (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have scalarRead : InRegions (s.rd ++ s.wr) (State.addr p.privateValue) p.privateLength :=
    ⟨⟨State.addr p.privateValue, p.privateLength⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have rootDomain : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domainRead, domS, by rw [← domLen]; exact domainBytes⟩
  have rootPeer : Octets p.base p.publicValue p.len yb s :=
    ⟨by rw [yLength]; exact yFit, by rw [yLength]; exact peerRead,
      by rw [yLength]; exact yS, by rw [yLength]; exact peerBytes⟩
  have rootScalar : Octets p.base p.privateValue p.len xb s :=
    ⟨by rw [xLength]; exact xFit, by rw [xLength]; exact scalarRead,
      by rw [xLength]; exact xS, by rw [xLength]; exact scalarBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit stackS, entered_octets rootDomain stackFit stackDom,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 7) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega)
  have argSub (i : Nat) (hi : i < 7) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 28⟩ := by
    rw [argStart, argAddr i hi]
    exact Offset.sub_base _ (by omega)
  have incoming (i : Nat) (hi : i < 7) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s stackFit (by omega)
      ⟨⟨stackArgAddr s 0, 28⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega) (by omega)⟩
      (stackArgs.sub_right (argSub i hi)) rfl
  have nativeIncoming : ExchangeIncoming p (entered s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h := incoming 0 (by decide)
      rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · rw [← scalar]; exact incoming 1 (by decide)
    · have h := incoming 2 (by decide)
      rw [← privateCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · rw [← peer]; exact incoming 3 (by decide)
    · rw [← base]; exact incoming 5 (by decide)
  have outWrite : InRegions (entered s).wr (State.addr p.output) p.k :=
    ⟨⟨State.addr p.output, p.k⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
  refine ⟨stackFit, args, nativeIncoming, out, domain, ?_,
    entered_octets rootPeer stackFit (by rw [yLength]; exact stackY), yLength,
    entered_octets rootScalar stackFit (by rw [xLength]; exact stackX),
    by rw [xLength]; omega, by rw [xLength]; have := p.maxLength; omega, ?_, ?_, ?_,
    ⟨outFit, outWrite⟩, outS.symm, stackOut.sub_left (locals_sub_reserved s stackFit), ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change BitVec.ofNat 32 p.privateLength = _; rw [xLength]
  · rw [yLength]; exact stackY.symm.sub_right (locals_sub_reserved s stackFit)
  · rw [xLength]; exact stackX.symm.sub_right (locals_sub_reserved s stackFit)
  · intro r hr
    simp only [exchangeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit
    · exact stackOut.sub_left (saved_sub_reserved s stackFit)

end VG.Proof.Ffdh.Arm
