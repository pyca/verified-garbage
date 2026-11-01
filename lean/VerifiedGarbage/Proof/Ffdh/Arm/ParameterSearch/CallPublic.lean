module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTCallState
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallLayout
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallFacts
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentWords
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallBytes
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! Equal public search positions supply equal public candidate arguments and entropy suffixes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem call_public {q : SearchPoint} {s t : State} (hs : CallCT q s) (ht : CallCT q t) (sp : s.sp = t.sp) :
    (Proof.Ffdh.sievedParameterCandidateContract abi 184).pub (callState q.inputs q.used s) (callState q.inputs q.used t) := by
  obtain ⟨originalS, liveS, roomS, argsS, memS, restS⟩ := hs
  obtain ⟨originalT, liveT, roomT, argsT, memT, restT⟩ := ht
  have spS : s.sp = originalS.sp - 24#32 := restS.sp
  have spT : t.sp = originalT.sp - 24#32 := restT.sp
  have memoryS : s.mem = callMem q.inputs q.used originalS.mem s.sp := by rw [spS]; exact memS
  have memoryT : t.mem = callMem q.inputs q.used originalT.mem t.sp := by rw [spT]; exact memT
  have factsS := liveS.buffers.callFacts q.used roomS
  have factsT := liveT.buffers.callFacts q.used roomT
  rw [← spS] at factsS
  rw [← spT] at factsT
  have a0S := call_stackArg (j := 0) factsS.argsFits memoryS (by decide)
  have a1S := call_stackArg (j := 1) factsS.argsFits memoryS (by decide)
  have a2S := call_stackArg (j := 2) factsS.argsFits memoryS (by decide)
  have a3S := call_stackArg (j := 3) factsS.argsFits memoryS (by decide)
  have a4S := call_stackArg (j := 4) factsS.argsFits memoryS (by decide)
  have a0T := call_stackArg (j := 0) factsT.argsFits memoryT (by decide)
  have a1T := call_stackArg (j := 1) factsT.argsFits memoryT (by decide)
  have a2T := call_stackArg (j := 2) factsT.argsFits memoryT (by decide)
  have a3T := call_stackArg (j := 3) factsT.argsFits memoryT (by decide)
  have a4T := call_stackArg (j := 4) factsT.argsFits memoryT (by decide)
  simp only [callValue] at a0S a1S a2S a3S a4S a0T a1T a2T a3T a4T
  have bytesS := liveS.call_bytes roomS memS
  have bytesT := liveT.call_bytes roomT memT
  have tapeNat : (BitVec.ofNat 32 (q.inputs.c.bytes.length - q.used)).toNat = q.inputs.c.bytes.length - q.used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := q.inputs.c.tapeCount; omega)]
  simp only [State.addr] at bytesS bytesT
  sig_pub [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [argsS.out, argsS.width, argsS.usedPtr, argsS.bits,
    argsT.out, argsT.width, argsT.usedPtr, argsT.bits,
    a0S, a1S, a2S, a3S, a4S, a0T, a1T, a2T, a3T, a4T, tapeNat]
  rw [bytesS, bytesT]
  simp only [sp, true_and]

end VG.Proof.Ffdh.Arm.ParameterSearch
