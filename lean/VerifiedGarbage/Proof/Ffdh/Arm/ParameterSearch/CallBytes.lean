module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Arguments
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Tape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! Preparing stack arguments leaves the remaining candidate entropy unchanged. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm

theorem SearchLive.call_bytes {p : SearchParams} {used remaining : Nat} {s u : State}
    (h : SearchLive p used remaining s) (room : used + p.c.length ≤ p.c.bytes.length)
    (mem : u.mem = callMem p used s.mem (s.sp - 24#32)) :
    Spec.Rsa.bytesAt u.mem (State.addr (p.c.tape + BitVec.ofNat 32 used))
      (p.c.bytes.length - used) = p.c.bytes.drop used := by
  rw [mem]
  refine (rsa_bytes_frame (callMem_frame p used s.mem (s.sp - 24#32))
    (by have := p.c.tapeCount; omega) ?_).trans (h.source_bytes room)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (((h.buffers.stackSeparate _ (by simp)).2.sub_left
    (callArguments_sub h.buffers.below)).sub_right (p.source_sub used room)).symm

end VG.Proof.Ffdh.Arm.ParameterSearch
