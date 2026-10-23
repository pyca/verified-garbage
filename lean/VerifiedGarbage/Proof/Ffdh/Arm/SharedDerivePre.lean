module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveFn
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! The derivation's signature supplies its native buffers and incoming argument words; it
reserves the outer frame plus the callable arithmetic stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem input (s : State) (pre : (Spec.Ffdh.derivePublicContract abi 176).pre s)
    {p : Inputs} {xb : List Byte}
    (base : stackArg s 3 = p.base) (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (scalar : stackArg s 1 = p.privateValue) (publicValue : p.publicValue = p.domain)
    (count : (stackArg s 0).toNat = p.k) (capacity : (stackArg s 4).toNat = p.len)
    (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    FnInput p xb s := by
  sig_pre [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, outDom, outX, outS, outArgs, domS, xS, sArgs,
    stackOut, stackDom, stackX, stackS, stackArgs, outFit, domFit, xFit, sFit,
    _, _, outLen, xPositive, xMax, _⟩ := pre
  have domLen : (s.gpr .r3).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [count] at outLen xMax
  rw [outLen] at wr outDom outX outS outArgs stackOut outFit
  rw [privateCount] at rd outX xS stackX xFit xPositive xMax
  rw [out] at wr outDom outX outS outArgs stackOut outFit
  rw [domain, domLen] at rd outDom domS stackDom domFit
  rw [scalar] at rd outX xS stackX xFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr outS domS xS sArgs stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackOut stackDom stackX stackS stackArgs
  have inner : Region.Sub (belowA s.sp 128) (belowA s.sp 176) := by
    simp only [belowA]
    rw [addr_sub' (by omega : 128 ≤ s.sp.toNat), addr_sub' stackFit]
    exact Offset.below_mono _ (by decide) (by decide)
  have stackFit' : 128 ≤ s.sp.toNat := by omega
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domainRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]),
      Region.contains_self _ _⟩
  have scalarRead : InRegions (s.rd ++ s.wr) (State.addr p.privateValue) p.privateLength :=
    ⟨⟨State.addr p.privateValue, p.privateLength⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]),
      Region.contains_self _ _⟩
  have rootDomain : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domainRead, domS, by rw [← domLen]; exact domainBytes⟩
  have rootScalar : Octets p.base p.privateValue p.len xb s :=
    ⟨by rw [xLength]; exact xFit, by rw [xLength]; exact scalarRead,
      by rw [xLength]; exact xS, by rw [xLength]; exact scalarBytes⟩
  have stackDom' := stackDom.sub_left inner
  have stackS' := stackS.sub_left inner
  have stackX' := stackX.sub_left inner
  have stackOut' := stackOut.sub_left inner
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit' stackS', entered_octets rootDomain stackFit' stackDom',
      stackDom'.symm.sub_right (locals_sub_reserved s stackFit'), by simp⟩
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 5) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega)
  have argSub (i : Nat) (hi : i < 5) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 20⟩ := by
    rw [argStart, argAddr i hi]
    exact Offset.sub_base _ (by omega)
  have incoming (i : Nat) (hi : i < 5) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s stackFit' (by omega)
      ⟨⟨stackArgAddr s 0, 20⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega) (by omega)⟩
      ((stackArgs.sub_left inner).sub_right (argSub i hi)) rfl
  have nativeIncoming : DeriveIncoming p (entered s) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := incoming 0 (by decide)
      rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · rw [← scalar]; exact incoming 1 (by decide)
    · have h := incoming 2 (by decide)
      rw [← privateCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · rw [← base]; exact incoming 3 (by decide)
  have outWrite : InRegions (entered s).wr (State.addr p.output) p.k :=
    ⟨⟨State.addr p.output, p.k⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])),
      Region.contains_self _ _⟩
  have pLen : p.k ≤ p.dom.length := by rw [p.domainLength]; split <;> omega
  have pubStack : Region.Disjoint ⟨State.addr p.publicValue, p.k⟩ (belowA s.sp 176) := by
    rw [publicValue]
    exact stackDom.symm.sub_left (Region.sub_prefix pLen)
  have calls := SharedExchange.CallMemory.of_outer (p := p) (n := xb.length) stackFit (entered_sp s)
    stackS stackDom.symm pubStack (by rw [xLength]; exact stackX.symm) stackOut.symm
  refine ⟨stackFit', args, nativeIncoming, calls, out, domain, ?_,
    entered_octets rootScalar stackFit' (by rw [xLength]; exact stackX'),
    by rw [xLength]; omega, by rw [xLength]; omega, ?_, ?_,
    ⟨outFit, outWrite⟩, outS.symm, stackOut'.sub_left (locals_sub_reserved s stackFit'), ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change BitVec.ofNat 32 p.privateLength = _; rw [xLength]
  · rw [xLength]; exact stackX'.symm.sub_right (locals_sub_reserved s stackFit')
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [exchangeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact stackS'.sub_left (saved_sub_reserved s stackFit')
      · exact saved_separate_locals s stackFit'
      · exact stackOut'.sub_left (saved_sub_reserved s stackFit')
    · have eq := List.mem_singleton.mp hr
      subst r
      have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
      have fit : (entered s).sp.toNat + 72 < 2^32 := by
        rw [entered_nat s stackFit']; have := s.sp.isLt; omega
      rw [shifted, VG.Arm.addr_add fit, belowA, addr_sub' calls.stack.fit]
      exact (Offset.disjoint_below_above _ (m := 48) (a := 72) (l := 56) (by decide)).symm

end VG.Proof.Ffdh.Arm.SharedDerive
