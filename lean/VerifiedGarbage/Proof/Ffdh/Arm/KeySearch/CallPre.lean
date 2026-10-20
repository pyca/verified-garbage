module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves

/-! The selected backend's shared precondition at the actual ARM call boundary. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem call_gpr (p : KeyPublic sampling) (used : Nat) (s : State) {r : Reg} (keep : r ∉ linkRegs) :
    (callState p used s).gpr r = s.gpr r :=
  State.callEntry_gpr s keep

theorem call_pre_legacy {p : KeyPublic sampling} {used keys scalars : Nat} {s : State} {m : Mem}
    (notcached : sampling.cachedContext = false) (facts : CallFacts p used) (h : ArgumentContext p used keys scalars s)
    (sp : s.sp = callSp p) (mem : s.mem = callMem p used m (callSp p)) :
    (GenerationPolicy.attemptContract sampling abi 176).pre (plainCallState p used s) := by
  have size : sampling.argumentBytes = 32 := by simp only [GenerationPolicy.argumentBytes, notcached, Bool.false_eq_true, ite_false]
  have plain : callRdPlain p used = [rDomain p, rTape p used, rCallArgs p] := by simp [callRdPlain, contextRegions, notcached]
  have selected : sampling.attemptContract abi 176 = sampling.legacyAttemptContract abi 176 := by cases sampling <;> simp_all only [GenerationPolicy.cachedContext, Bool.true_eq_false] <;> rfl
  have a0 := call_stackArg (j := 0) facts sp mem (by cases sampling <;> decide)
  have a1 := call_stackArg (j := 1) facts sp mem (by cases sampling <;> decide)
  have a2 := call_stackArg (j := 2) facts sp mem (by cases sampling <;> decide)
  have a3 := call_stackArg (j := 3) facts sp mem (by cases sampling <;> decide)
  have a4 := call_stackArg (j := 4) facts sp mem (by cases sampling <;> decide)
  have a5 := call_stackArg (j := 5) facts sp mem (by cases sampling <;> decide)
  have a6 := call_stackArg (j := 6) facts sp mem (by cases sampling <;> decide)
  change stackArg (plainCallState p used s) 0 = callValue p used 0 at a0
  change stackArg (plainCallState p used s) 1 = callValue p used 1 at a1
  change stackArg (plainCallState p used s) 2 = callValue p used 2 at a2
  change stackArg (plainCallState p used s) 3 = callValue p used 3 at a3
  change stackArg (plainCallState p used s) 4 = callValue p used 4 at a4
  change stackArg (plainCallState p used s) 5 = callValue p used 5 at a5
  change stackArg (plainCallState p used s) 6 = callValue p used 6 at a6
  simp only [callValue] at a0 a1 a2 a3 a4 a5 a6
  have argAddr : stackArgAddr (plainCallState p used s) 0 = State.addr (callSp p) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact congrArg State.addr sp
  have nativeLen : (BitVec.ofNat 32 p.len).toNat = p.len :=
    Nat.mod_eq_of_lt facts.lenFits
  have domainLen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen :=
    Nat.mod_eq_of_lt facts.domainLenFits
  have capacity : (BitVec.ofNat 32 p.capacity).toNat = p.capacity :=
    Nat.mod_eq_of_lt facts.capacityFits
  rw [selected]
  sig_pre [GenerationPolicy.legacyAttemptContract, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.x, h.xlen, h.y, h.ylen,
    a0, a1, a2, a3, a4, a5, a6, nativeLen, domainLen, capacity, argAddr, sp, plain]
  have stack (r : Region) (member : r ∈ [rX p, rY p, rDomain p, rTape p used, rScratch p, rCallArgs p]) :
      (⟨State.addr (callSp p) - 176#64, 176⟩ : Region).Disjoint r := by
    rw [← FrameStack.addr_sub' facts.stackFits]
    exact facts.stack r member
  have xa : (rX p).Disjoint ⟨State.addr (callSp p), 28⟩ := by simpa only [rCallArgs, size, Nat.reduceSub] using facts.xa
  have ya : (rY p).Disjoint ⟨State.addr (callSp p), 28⟩ := by simpa only [rCallArgs, size, Nat.reduceSub] using facts.ya
  have sa : (rScratch p).Disjoint ⟨State.addr (callSp p), 28⟩ := by simpa only [rCallArgs, size, Nat.reduceSub] using facts.sa
  refine ⟨facts.stackFits, ?_, ?_, ?_, facts.xy, facts.xd, facts.xr, facts.xs, xa,
    facts.yd, facts.yr, facts.ys, ya, facts.ds, facts.rs, sa,
    stack (rX p) (by simp), stack (rY p) (by simp), stack (rDomain p) (by simp),
    stack (rTape p used) (by simp), stack (rScratch p) (by simp), ?_, facts.xFit, facts.yFit, facts.domainFit, facts.tapeFit,
    facts.scratchFit, facts.length, facts.domainLength, trivial, trivial, trivial, facts.scratch⟩
  · have argsFit := facts.argsFit; simp only [GenerationPolicy.argumentBytes, notcached, Bool.false_eq_true, ite_false, Nat.reduceSub] at argsFit; omega
  · simp only [rCallArgs, size, Nat.reduceSub]; rfl
  · rfl
  · simpa only [rCallArgs, size, Nat.reduceSub, State.addr] using stack (rCallArgs p) (by simp)


theorem call_pre_cached {p : KeyPublic .cached} {used keys scalars : Nat} {original v s : State}
    (live : KeyLive p original used keys scalars v) (room : used + p.len ≤ p.randLen)
    (h : ArgumentContext p used keys scalars s)
    (sp : s.sp = callSp p) (mem : s.mem = callMem p used v.mem (callSp p)) :
    (GenerationPolicy.attemptContract .cached abi 176).pre (plainCallState p used s) := by
  have facts := live.input.callFacts room
  have a0 := call_stackArg (j := 0) facts sp mem (by decide)
  have a1 := call_stackArg (j := 1) facts sp mem (by decide)
  have a2 := call_stackArg (j := 2) facts sp mem (by decide)
  have a3 := call_stackArg (j := 3) facts sp mem (by decide)
  have a4 := call_stackArg (j := 4) facts sp mem (by decide)
  have a5 := call_stackArg (j := 5) facts sp mem (by decide)
  have a6 := call_stackArg (j := 6) facts sp mem (by decide)
  have a7 := call_stackArg (j := 7) facts sp mem (by decide)
  have a8 := call_stackArg (j := 8) facts sp mem (by decide)
  change stackArg (plainCallState p used s) 0 = callValue p used 0 at a0
  change stackArg (plainCallState p used s) 1 = callValue p used 1 at a1
  change stackArg (plainCallState p used s) 2 = callValue p used 2 at a2
  change stackArg (plainCallState p used s) 3 = callValue p used 3 at a3
  change stackArg (plainCallState p used s) 4 = callValue p used 4 at a4
  change stackArg (plainCallState p used s) 5 = callValue p used 5 at a5
  change stackArg (plainCallState p used s) 6 = callValue p used 6 at a6
  change stackArg (plainCallState p used s) 7 = callValue p used 7 at a7
  change stackArg (plainCallState p used s) 8 = callValue p used 8 at a8
  simp only [callValue] at a0 a1 a2 a3 a4 a5 a6 a7 a8
  have argAddr : stackArgAddr (plainCallState p used s) 0 = State.addr (callSp p) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact congrArg State.addr sp
  have nativeLen : (BitVec.ofNat 32 p.len).toNat = p.len := Nat.mod_eq_of_lt facts.lenFits
  have domainLen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen := Nat.mod_eq_of_lt facts.domainLenFits
  have capacity : (BitVec.ofNat 32 p.capacity).toNat = p.capacity := Nat.mod_eq_of_lt facts.capacityFits
  have ctxFit := live.input.context_fit rfl
  have ctxLen : (BitVec.ofNat 32 p.contextWords).toNat = p.contextWords := Nat.mod_eq_of_lt (by omega)
  have read : rContext p ∈ original.rd := by rw [live.input.read_regions]; simp [contextRegions, GenerationPolicy.cachedContext]
  have sep := live.input.call_read read
  have frame : Frame (callChanges p) v.mem s.mem := by
    rw [mem]; exact (callMem_frame _ _ _ _).mono (by simp [callChanges, rArguments])
  have held := live.cachedHeld.after_frame frame (by intro _; omega) (by intro _; exact sep)
  have canonical := held rfl
  have dom := (live.input.call_domain_frame frame).trans live.domain
  have valid := live.input.bounds.domainValid
  have xy := facts.xy
  have xd := facts.xd
  have xr := facts.xr
  have xs := facts.xs
  have xa := facts.xa
  have yd := facts.yd
  have yr := facts.yr
  have ys := facts.ys
  have ya := facts.ya
  have ds := facts.ds
  have rs := facts.rs
  have sa := facts.sa
  have xc := (sep (rX p) (by simp [callChanges])).symm
  have yc := (sep (rY p) (by simp [callChanges])).symm
  have sc := (sep (rScratch p) (by simp [callChanges])).symm
  have cs := (sep (rCallStack p) (by simp [callChanges])).symm
  have sx := facts.stack (rX p) (by simp)
  have sy := facts.stack (rY p) (by simp)
  have sd := facts.stack (rDomain p) (by simp)
  have sr := facts.stack (rTape p used) (by simp)
  have ss := facts.stack (rScratch p) (by simp)
  have saa := facts.stack (rCallArgs p) (by simp)
  have stackFit := facts.stackFits
  have argFit := facts.argsFit
  have xFit := facts.xFit
  have yFit := facts.yFit
  have dFit := facts.domainFit
  have rFit := facts.tapeFit
  have sFit := facts.scratchFit
  have length := facts.length
  have domainLength := facts.domainLength
  have scratch := facts.scratch
  sig_pre [GenerationPolicy.attemptContract, cachedGenerateKeyContract, cachedGenerateKeySig,
    generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.x, h.xlen, h.y, h.ylen, a0, a1, a2, a3, a4, a5, a6, a7, a8,
    nativeLen, domainLen, capacity, ctxLen, argAddr, sp]
  simp only [rX, rY, rDomain, rTape, rScratch, rCallArgs, rContext, rCallStack,
    GenerationPolicy.argumentBytes, GenerationPolicy.cachedContext, ite_true, Nat.reduceSub,
    FrameStack.belowA, State.addr,
    callRdPlain, callWr, contextRegions, List.cons_append, List.nil_append] at *
  have subAddr := FrameStack.addr_sub' stackFit
  simp only [State.addr] at subAddr
  rw [subAddr] at cs sx sy sd sr ss saa
  simp only [Nat.mul_comm] at *
  simp only [dom]
  sig_and_intros
  sig_close
  all_goals exact True.intro

 theorem call_pre_plain {p : KeyPublic sampling} {used keys scalars : Nat} {original v s : State}
    (live : KeyLive p original used keys scalars v) (room : used + p.len ≤ p.randLen)
    (h : ArgumentContext p used keys scalars s)
    (sp : s.sp = callSp p) (mem : s.mem = callMem p used v.mem (callSp p)) :
    (GenerationPolicy.attemptContract sampling abi 176).pre (plainCallState p used s) := by
  cases sampling with
  | full => exact call_pre_legacy rfl (live.input.callFacts room) h sp mem
  | vetted => exact call_pre_legacy rfl (live.input.callFacts room) h sp mem
  | cached => exact call_pre_cached live room h sp mem

end VG.Proof.Ffdh.Arm.KeySearch
