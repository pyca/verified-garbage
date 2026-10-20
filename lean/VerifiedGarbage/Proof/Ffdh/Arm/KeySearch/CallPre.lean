module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! The selected backend's shared precondition at the actual ARM call boundary. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem call_gpr (p : KeyPublic) (used : Nat) (s : State) {r : Reg} (keep : r ∉ linkRegs) :
    (callState p used s).gpr r = s.gpr r :=
  State.callEntry_gpr s keep

theorem call_pre {p : KeyPublic} {used keys scalars : Nat} {s : State} {m : Mem}
    (facts : CallFacts p used) (h : ArgumentContext p used keys scalars s)
    (sp : s.sp = callSp p) (mem : s.mem = callMem p used m (callSp p)) :
    (generateKeyContract abi 176).pre (callState p used s) := by
  have a0 := call_stackArg (j := 0) facts sp mem (by decide)
  have a1 := call_stackArg (j := 1) facts sp mem (by decide)
  have a2 := call_stackArg (j := 2) facts sp mem (by decide)
  have a3 := call_stackArg (j := 3) facts sp mem (by decide)
  have a4 := call_stackArg (j := 4) facts sp mem (by decide)
  have a5 := call_stackArg (j := 5) facts sp mem (by decide)
  have a6 := call_stackArg (j := 6) facts sp mem (by decide)
  simp only [callValue] at a0 a1 a2 a3 a4 a5 a6
  have argAddr : stackArgAddr (callState p used s) 0 = State.addr (callSp p) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact congrArg State.addr sp
  have nativeLen : (BitVec.ofNat 32 p.len).toNat = p.len :=
    Nat.mod_eq_of_lt facts.lenFits
  have domainLen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen :=
    Nat.mod_eq_of_lt facts.domainLenFits
  have capacity : (BitVec.ofNat 32 p.capacity).toNat = p.capacity :=
    Nat.mod_eq_of_lt facts.capacityFits
  sig_pre [generateKeyContract, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.x, h.xlen, h.y, h.ylen,
    a0, a1, a2, a3, a4, a5, a6, nativeLen, domainLen, capacity, argAddr, sp]
  have stack (r : Region) (member : r ∈ [rX p, rY p, rDomain p, rTape p used, rScratch p, rCallArgs p]) :
      (⟨State.addr (callSp p) - 176#64, 176⟩ : Region).Disjoint r := by
    rw [← FrameStack.addr_sub' facts.stackFits]
    exact facts.stack r member
  refine ⟨facts.stackFits, ?_, ?_, ?_, facts.xy, facts.xd, facts.xr, facts.xs, facts.xa,
    facts.yd, facts.yr, facts.ys, facts.ya, facts.ds, facts.rs, facts.sa,
    stack (rX p) (by simp), stack (rY p) (by simp), stack (rDomain p) (by simp),
    stack (rTape p used) (by simp), stack (rScratch p) (by simp), ?_, facts.xFit, facts.yFit, facts.domainFit, facts.tapeFit,
    facts.scratchFit, facts.length, facts.domainLength, trivial, trivial, trivial, facts.scratch⟩
  · have := facts.argsFit; omega
  · rfl
  · rfl
  · exact stack (rCallArgs p) (by simp)

end VG.Proof.Ffdh.Arm.KeySearch
