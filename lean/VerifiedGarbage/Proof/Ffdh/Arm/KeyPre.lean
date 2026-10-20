module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! The shared key-generation signature supplies native entropy and writable key buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem key_input (s : State) (pre : (Spec.Ffdh.generateKeyContract abi 128).pre s)
    {p : Inputs} {rb : List Byte}
    (base : stackArg s 5 = p.base) (privateValue : s.gpr .r0 = p.privateValue)
    (publicValue : s.gpr .r2 = p.publicValue) (domain : stackArg s 0 = p.domain)
    (count : (stackArg s 2).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (entropy : stackArg s 3 = p.entropy) (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb) :
    KeyFnInput p rb s := by
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre

  obtain ⟨stackFit, argFit, rd, wr, xY, xDom, xRand, xS, xArgs, yDom, yRand, yS, yArgs,
    domS, randS, sArgs, stackX, stackY, stackDom, stackRand, stackS, stackArgs,
    xFit, yFit, domFit, randFit, sFit, _, _, xLen, yLen, rLen, _⟩ := pre
  have domLen : (stackArg s 1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have randLength : rb.length = p.k := by
    have eq := congrArg List.length entropyBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [count] at xLen yLen rLen
  rw [xLen] at wr xY xDom xRand xS xArgs stackX xFit
  rw [yLen] at wr xY yDom yRand yS yArgs stackY yFit
  rw [rLen] at rd xRand yRand randS stackRand randFit
  rw [privateValue] at wr xY xDom xRand xS xArgs stackX xFit
  rw [publicValue] at wr xY yDom yRand yS yArgs stackY yFit
  rw [domain, domLen] at rd xDom yDom domS stackDom domFit
  rw [entropy] at rd xRand yRand randS stackRand randFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr xS yS domS randS sArgs stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackX stackY stackDom stackRand stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domainRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have entropyRead : InRegions (s.rd ++ s.wr) (State.addr p.entropy) p.k :=
    ⟨⟨State.addr p.entropy, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have rootDomain : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domainRead, domS, by rw [← domLen]; exact domainBytes⟩
  have rootEntropy : Octets p.base p.entropy p.len rb s :=
    ⟨by rw [randLength]; exact randFit, by rw [randLength]; exact entropyRead,
      by rw [randLength]; exact randS, by rw [randLength]; exact entropyBytes⟩
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
  have nativeIncoming : KeyIncoming p (entered s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← domain]; exact incoming 0 (by decide)
    · have h := incoming 1 (by decide)
      rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · have h := incoming 2 (by decide)
      rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · rw [← entropy]; exact incoming 3 (by decide)
    · rw [← base]; exact incoming 5 (by decide)
  have xWrite : InRegions (entered s).wr (State.addr p.privateValue) p.k :=
    ⟨⟨State.addr p.privateValue, p.k⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
  have yWrite : InRegions (entered s).wr (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
  have outputs : KeyOutputs p (entered s) :=
    ⟨⟨xFit, xWrite⟩, ⟨yFit, yWrite⟩, xDom.symm, yDom.symm,
      stackX.sub_left (locals_sub_reserved s stackFit), stackY.sub_left (locals_sub_reserved s stackFit),
      xS, yS, xY⟩
  refine ⟨stackFit, args, nativeIncoming, privateValue, publicValue, outputY, privateLength,
    entered_octets rootEntropy stackFit (by rw [randLength]; exact stackRand), randLength,
    stackRand.symm.sub_right (locals_sub_reserved s stackFit), outputs, xRand.symm, ?_⟩
  intro r hr
  simp only [keyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact stackS.sub_left (saved_sub_reserved s stackFit)
  · exact saved_separate_locals s stackFit
  · exact stackX.sub_left (saved_sub_reserved s stackFit)
  · exact stackY.sub_left (saved_sub_reserved s stackFit)

end VG.Proof.Ffdh.Arm
