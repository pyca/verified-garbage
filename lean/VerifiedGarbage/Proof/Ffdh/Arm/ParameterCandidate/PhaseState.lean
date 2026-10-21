module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Spec.Ffdh

/-! The public parameter-generation phase's four saved policy words. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

def phaseBits (q : Bool) (bits : Nat) : Nat := if q then bits - 1 else bits

def phaseMemory (s : State) (q : Bool) (bits : Nat) : Mem :=
  (((s.mem.writeW (State.addr (s.sp + 44#32)) (BitVec.ofNat 32 (phaseBits q bits))).writeW
    (State.addr (s.sp + 48#32)) (BitVec.ofNat 32 ((phaseBits q bits + 7) / 8))).writeW
    (State.addr (s.sp + 52#32)) (BitVec.ofNat 32 (VG.Spec.Ffdh.primeChecks (phaseBits q bits)))).writeW
    (State.addr (s.sp + 56#32)) (0#32)



end VG.Proof.Ffdh.Arm.ParameterCandidate
