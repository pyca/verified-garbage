module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPre
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! The enlarged stack reservation supplies the shared arithmetic calls. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm

theorem keyGenerate_pre128 (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 176).pre s) :
    (Spec.Ffdh.generateKeyContract abi 128).pre s := by
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre ⊢
  obtain ⟨stackFit, argFit, rd, wr, xY, xDom, xRand, xS, xArgs, yDom, yRand, yS, yArgs,
    domS, randS, sArgs, stackX, stackY, stackDom, stackRand, stackS, stackArgs,
    xFit, yFit, domFit, randFit, sFit, bounds, domainLen, xLen, yLen, rLen, space⟩ := pre
  have inner : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 128, 128⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 176, 176⟩ :=
    Offset.below_mono _ (by decide) (by decide)
  exact ⟨by omega, argFit, rd, wr, xY, xDom, xRand, xS, xArgs, yDom, yRand, yS, yArgs,
    domS, randS, sArgs, stackX.sub_left inner, stackY.sub_left inner, stackDom.sub_left inner,
    stackRand.sub_left inner, stackS.sub_left inner, stackArgs.sub_left inner,
    xFit, yFit, domFit, randFit, sFit, bounds, domainLen, xLen, yLen, rLen, space⟩

theorem keyGenerate_input (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 176).pre s)
    {p : Inputs} {rb : List Byte}
    (base : stackArg s 5 = p.base) (privateValue : s.gpr .r0 = p.privateValue)
    (publicValue : s.gpr .r2 = p.publicValue) (domain : stackArg s 0 = p.domain)
    (count : (stackArg s 2).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (entropy : stackArg s 3 = p.entropy) (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb) :
    KeyGenerateFnInput p rb s := by
  have old := key_input s (keyGenerate_pre128 s pre) base privateValue publicValue domain count capacity
    entropy outputY privateLength domainBytes entropyBytes
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stackX, stackY, stackDom, stackRand, stackS, _,
    _, _, _, _, _, _, _, xLen, yLen, rLen, _⟩ := pre
  have domLen : (stackArg s 1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [count] at xLen yLen rLen
  rw [xLen, privateValue] at stackX
  rw [yLen, publicValue] at stackY
  rw [domain, domLen] at stackDom
  rw [rLen, entropy] at stackRand
  rw [base, capacity, Nat.mul_comm p.len 8] at stackS
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackX stackY stackDom stackRand stackS
  have calls := KeyCallMemory.of_outer stackFit (entered_sp s) stackS stackDom.symm stackX.symm stackY.symm stackRand.symm old.outputs.privateBuffer.fits
  refine ⟨old, calls, ?_⟩
  have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
  have fit : (entered s).sp.toNat + 72 < 2 ^ 32 := by
    rw [entered_nat s (by omega)]; have := s.sp.isLt; omega
  rw [shifted, VG.Arm.addr_add fit, belowA, addr_sub' calls.stack.fit]
  exact (Offset.disjoint_below_above _ (m := 48) (a := 72) (l := 56) (by decide)).symm

end VG.Proof.Ffdh.Arm
