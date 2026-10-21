module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Public
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Normalize the existing public signature's memory layout without changing its separation requirements. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

def readRegions (p : SearchParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.c.tape, p.c.bytes.length⟩, ⟨State.addr sp, 24⟩]

def writeRegions (p : SearchParams) : List Region :=
  [⟨State.addr p.c.out, p.c.length⟩, ⟨State.addr p.c.usedPtr, 8⟩,
    ⟨State.addr p.c.base, 8 * p.c.capacity⟩, ⟨State.addr p.control, 128⟩]

structure SearchLayout (p : SearchParams) (s : State) : Prop where
  stackFits : 232 ≤ s.sp.toNat
  argsFits : s.sp.toNat + 24 ≤ 2 ^ 32
  reads : s.rd = readRegions p s.sp
  writes : s.wr = writeRegions p
  controlArgs : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, 24⟩
  stackSeparate : ∀ r ∈ writeRegions p ++ readRegions p s.sp, (FrameStack.belowA s.sp 232).Disjoint r

theorem searchLayout {p : SearchParams} {s : State}
    (pre : (Spec.Ffdh.parameterSearchContract abi 232).pre s) (args : SearchAbi p s) : SearchLayout p s := by
  sig_pre [Spec.Ffdh.parameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, _, _, _, _, _, _, _, _, _, _, controlArgs,
    stackOut, stackUsed, stackTape, stackScratch, stackControl, stackArgs, _⟩ := pre
  have widthNat : (s.gpr .r1).toNat = p.c.length := by
    rw [args.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.width_bounds; omega)]
  have tapeNat : (stackArg s 2).toNat = p.c.bytes.length := by
    rw [args.tapeLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.c.tapeCount]
  have capNat : (stackArg s 4).toNat = p.c.capacity := by
    rw [args.capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.capacity_fits]
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have reserved : s.sp.setWidth 64 - 232#64 = State.addr (s.sp - 232#32) :=
    (FrameStack.addr_sub' stackFit).symm
  rw [args.out, args.used, args.base, args.control, widthNat, capNat, Nat.mul_comm p.c.capacity 8] at wr
  rw [args.tape, tapeNat, argStart] at rd
  rw [args.control, argStart] at controlArgs
  rw [args.out, widthNat, reserved] at stackOut
  rw [args.used, reserved] at stackUsed
  rw [args.tape, tapeNat, reserved] at stackTape
  rw [args.base, capNat, Nat.mul_comm p.c.capacity 8, reserved] at stackScratch
  rw [args.control, reserved] at stackControl
  rw [argStart, reserved] at stackArgs
  refine ⟨stackFit, argFit, rd, wr, controlArgs, ?_⟩
  intro r member
  simp only [writeRegions, readRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact stackOut
  · exact stackUsed
  · exact stackScratch
  · exact stackControl
  · exact stackTape
  · exact stackArgs

end VG.Proof.Ffdh.Arm.ParameterSearch
