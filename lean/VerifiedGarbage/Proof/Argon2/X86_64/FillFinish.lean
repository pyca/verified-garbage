module

public import VerifiedGarbage.Impl.Argon2.X86_64.FillFinish
public import VerifiedGarbage.Impl.Argon2.X86_64.FillIterations
public import VerifiedGarbage.Impl.Argon2.X86_64.FillIteration
public import VerifiedGarbage.Impl.Argon2.X86_64.FillSlices
public import VerifiedGarbage.Impl.Argon2.X86_64.FillSlice
public import VerifiedGarbage.Impl.Argon2.X86_64.FillLanes
public import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupPrepare
import VerifiedGarbage.Proof.Argon2.X86_64.FillLaneAdvance
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup
public import VerifiedGarbage.Proof.Argon2.Lanes
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.Iterations
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Impl.Argon2.X86_64.FinalReduction
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
import VerifiedGarbage.Proof.Argon2.Dimensions
meta import VerifiedGarbage.Impl.Argon2.X86_64.FinalReduction
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState
meta import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupPrepare
meta import VerifiedGarbage.Proof.Argon2.X86_64.FillLaneAdvance
meta import VerifiedGarbage.Proof.Argon2.Dimensions
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
import VerifiedGarbage.Proof.MdStream.X86_64.Common
public import VerifiedGarbage.Impl.Argon2.X86_64.FinalOutput
public import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLane
import VerifiedGarbage.Proof.Argon2.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
meta import VerifiedGarbage.Proof.MdStream.X86_64.Common
meta import VerifiedGarbage.Impl.Argon2.X86_64.FinalOutput
meta import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLane
meta import VerifiedGarbage.Proof.Argon2.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Argon2.X86_64.FinishReady`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.FinalOutputReady`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.MemoryInitCall`, which this module and modules that import it used -/

section

/-! # A verified H′ call to initialize a memory block -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_nosp (v : Proof.Blake2.X86_64.Backend) : NoSp (code (HPrime.hash v)) := by
  have all (c : Prog isa) (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi; simp only [h i hi, Bool.not_false]
  have hi := all _ (HPrime.hash_ok v).initNoSp
  have hu := all _ (HPrime.hash_ok v).updateNoSp
  have hf := all _ (HPrime.hash_ok v).finalizeNoSp
  have check : (code (HPrime.hash v)).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    simp only [code, setup, saved, first, chooseLength, init, initArgs, absorbFixed,
      fixedArgs, update, updateArgs, absorbInput, inputArgs, finishInput, finalize,
      finalizeArgs, finishOutput, extendDigest, emitPrefix, copy, copyByte, chain,
      next, copyRemaining, restore, Code.allInstrs]
    rw [hi, hu, hf]
    decide +kernel
  rw [Code.allInstrs_eq, List.all_eq_true] at check
  intro i hi
  simpa only [Bool.not_eq_true'] using check i hi

theorem hPrime_depth (v : Proof.Blake2.X86_64.Backend) : (code (HPrime.hash v)).depth = 2 := by
  simp only [code, first, chooseLength, init, absorbFixed, update, absorbInput,
    finishInput, finalize, finishOutput, extendDigest, emitPrefix, copy, chain,
    next, copyRemaining, Code.depth, (HPrime.hash_ok v).initDepth,
    (HPrime.hash_ok v).updateDepth, (HPrime.hash_ok v).finalizeDepth]
  rfl

structure CallReady (s : State) : Prop where
  input : Covers [⟨s.gpr .rdi, 72⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .rdx, 1024⟩] s.wr
  work : (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .rdi, 72⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  outputWork : (⟨s.gpr .rdx, 1024⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  stackInput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 72⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, 1024⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .r8, 16384⟩

structure Called (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .rdx) 1024 = Spec.Argon2.hPrime 1024 (bytesAt s.mem (s.gpr .rdi) 72)
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩, below (s.gpr .rsp) 24] s.mem t.mem

theorem hPrime_call_hyps (s : State) (h : CallReady s)
    (inputLength : s.gpr .rsi = 72) (outputLength : s.gpr .rcx = 1024) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .rdi, 72⟩]
      [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩]) ∧
    Covers [⟨s.gpr .rdi, 72⟩, ⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩] s.wr := by
  have g : ∀ r, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  have inner := below_callee (s.gpr .rsp) 16
  have ret := below_sub (sp := s.gpr .rsp) (by decide : 8 ≤ 24) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, HPrime.retR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), g _ (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_rsp, inputLength, outputLength]
    exact ⟨rfl, rfl, by decide, by decide, by decide, h.inputWork, h.outputWork,
      h.stackInput.sub_left inner, h.stackOutput.sub_left inner, h.stackWork.sub_left inner,
      h.stackOutput.sub_left ret, h.stackWork.sub_left ret⟩
  · intro p n hp
    rcases hp with ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · exact ⟨_, List.mem_append_right _ h.work, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, h.work, hc⟩

theorem hPrime_call_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (h : CallReady s) (inputLength : s.gpr .rsi = 72)
    (outputLength : s.gpr .rcx = 1024) :
    WP isa (.call name (code (HPrime.hash v))) s (Called s) := by
  obtain ⟨pre, cover, writes⟩ := hPrime_call_hyps s h inputLength outputLength
  refine WP.call (k := HPrime.localContract) (HPrime.code_correct v) (hPrime_nosp v)
    (by rw [hPrime_depth]; decide) pre cover writes ?_
  intro t rd wr regs frame _ ⟨u, memU, regsU, digest⟩
  have inputBytes : bytesAt s.callEntry.mem (s.gpr .rdi) 72 = bytesAt s.mem (s.gpr .rdi) 72 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact Proof.MdStream.X86_64.callEntry_byte s (h.stackInput.sub_left
      (below_sub (by decide) (by decide))) (show (72 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine ⟨?_, regs, rd, wr, ?_⟩
  · change bytesAt u.mem (s.callEntry.gpr .rdx) (s.callEntry.gpr .rcx).toNat =
      Spec.Argon2.hPrime (s.callEntry.gpr .rcx).toNat
        (bytesAt s.callEntry.mem (s.callEntry.gpr .rdi) (s.callEntry.gpr .rsi).toNat) at digest
    rw [State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      memU, inputLength, outputLength,
      show (72 : Addr).toNat = 72 from rfl,
      show (1024 : Addr).toNat = 1024 from rfl, inputBytes] at digest
    exact digest
  · rw [hPrime_depth] at frame
    exact frame

end VG.Proof.Argon2.X86_64.MemoryInit

end

end

/-! ### `Argon2.X86_64.FinalCall`, which only this module used -/

section

/-! The final H′ call accepts a complete reduced block and a public tag length. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FinalCall

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (code)
open VG.Spec.Blake2 (bytesAt)

structure CallReady (len : Nat) (s : State) : Prop where
  positive : 1 ≤ len
  bound : len < 2 ^ 32
  input : Covers [⟨s.gpr .rdi, 1024⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .rdx, len⟩] s.wr
  work : (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  outputWork : (⟨s.gpr .rdx, len⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  stackInput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 1024⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, len⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .r8, 16384⟩

structure Called (len : Nat) (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .rdx) len = Spec.Argon2.hPrime len (bytesAt s.mem (s.gpr .rdi) 1024)
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rdx, len⟩, ⟨s.gpr .r8, 16384⟩, below (s.gpr .rsp) 24] s.mem t.mem

theorem hPrime_call_hyps (len : Nat) (s : State) (h : CallReady len s)
    (inputLength : s.gpr .rsi = 1024) (outputLength : s.gpr .rcx = BitVec.ofNat 64 len) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .rdi, 1024⟩]
      [⟨s.gpr .rdx, len⟩, ⟨s.gpr .r8, 16384⟩]) ∧
    Covers [⟨s.gpr .rdi, 1024⟩, ⟨s.gpr .rdx, len⟩, ⟨s.gpr .r8, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .rdx, len⟩, ⟨s.gpr .r8, 16384⟩] s.wr := by
  have length : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bound (by decide))]
  have g : ∀ r, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  have inner := below_callee (s.gpr .rsp) 16
  have ret := below_sub (sp := s.gpr .rsp) (by decide : 8 ≤ 24) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, HPrime.retR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), g _ (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_rsp, inputLength, outputLength, length]
    exact ⟨rfl, trivial, by decide, h.positive, h.bound, h.inputWork, h.outputWork,
      h.stackInput.sub_left inner, h.stackOutput.sub_left inner, h.stackWork.sub_left inner,
      h.stackOutput.sub_left ret, h.stackWork.sub_left ret⟩
  · intro p n hp
    rcases hp with ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · exact ⟨_, List.mem_append_right _ h.work, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, h.work, hc⟩

theorem hPrime_call_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (len : Nat) (s : State) (h : CallReady len s) (inputLength : s.gpr .rsi = 1024)
    (outputLength : s.gpr .rcx = BitVec.ofNat 64 len) :
    WP isa (.call name (code (HPrime.hash v))) s (Called len s) := by
  obtain ⟨pre, cover, writes⟩ := hPrime_call_hyps len s h inputLength outputLength
  refine WP.call (k := HPrime.localContract) (HPrime.code_correct v) (MemoryInit.hPrime_nosp v)
    (by rw [MemoryInit.hPrime_depth]; decide) pre cover writes ?_
  intro t rd wr regs frame _ ⟨u, memU, regsU, digest⟩
  have inputBytes : bytesAt s.callEntry.mem (s.gpr .rdi) 1024 = bytesAt s.mem (s.gpr .rdi) 1024 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact Proof.MdStream.X86_64.callEntry_byte s (h.stackInput.sub_left
      (below_sub (by decide) (by decide))) (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine ⟨?_, regs, rd, wr, ?_⟩
  · change bytesAt u.mem (s.callEntry.gpr .rdx) (s.callEntry.gpr .rcx).toNat =
      Spec.Argon2.hPrime (s.callEntry.gpr .rcx).toNat
        (bytesAt s.callEntry.mem (s.callEntry.gpr .rdi) (s.callEntry.gpr .rsi).toNat) at digest
    rw [State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      memU, inputLength, outputLength,
      show (1024 : Addr).toNat = 1024 from rfl,
      show (BitVec.ofNat 64 len).toNat = len from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bound (by decide))], inputBytes] at digest
    exact digest
  · rw [MemoryInit.hPrime_depth] at frame
    exact frame

end VG.Proof.Argon2.X86_64.FinalCall

end

end


/-! Merged from `Proof.Argon2.X86_64.FinalOutputArgs`. -/

@[expose] public section

section
/-! Load the public final-call pointers and tag length from the enclosing frame. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2

def output (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 256) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def changed : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8]

structure Arguments (s t : State) : Prop where
  input : t.gpr .rdi = ReductionState.matrix s
  inputLength : t.gpr .rsi = 1024
  output : t.gpr .rdx = output s
  outputLength : t.gpr .rcx = s.mem.readW (off (s.gpr .rbp) 264) 64
  work : t.gpr .r8 = work s
  keeps : Divide.Keeps changed s t

theorem args_ok (s : State) (read : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    WP isa (.block Impl.Argon2.X86_64.FinalOutput.args) s (Arguments s) := by
  have input := read 232 (by simp)
  have out := read 256 (by simp)
  have len := read 264 (by simp)
  have scratch := read 248 (by simp)
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FinalOutput.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    input, out, len, scratch, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem Arguments.regs {s t : State} (h : Arguments s t) (r : Reg) (hr : r ∈ calleeSaved) : t.gpr r = s.gpr r := by
  have unchanged : r ∉ changed := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.keeps.regs r unchanged

end VG.Proof.Argon2.X86_64.FinalOutput
end

/-! Final output uses matrix block zero and the original disjoint hash scratch allocation. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  positive : 1 ≤ p.tagLen
  bound : p.tagLen < 2 ^ 32
  reads : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  tagWord : s.mem.readW (off (s.gpr .rbp) 264) 64 = BitVec.ofNat 64 p.tagLen
  input : Covers [⟨ReductionState.matrix s, 1024⟩] (s.rd ++ s.wr)
  outputWrite : Covers [⟨output s, p.tagLen⟩] s.wr
  workWrite : (⟨work s, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨ReductionState.matrix s, 1024⟩ : Region).Disjoint ⟨work s, 16384⟩
  outputWork : (⟨output s, p.tagLen⟩ : Region).Disjoint ⟨work s, 16384⟩
  stackInput : (below (s.gpr .rsp) 24).Disjoint ⟨ReductionState.matrix s, 1024⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨output s, p.tagLen⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨work s, 16384⟩

theorem Arguments.ready {p : Params} {s t : State} (h : Ready p s) (a : Arguments s t) :
    FinalCall.CallReady p.tagLen t := by
  have sp := a.regs .rsp (by simp [calleeSaved])
  constructor
  · exact h.positive
  · exact h.bound
  · rw [a.input, a.keeps.rd, a.keeps.wr]; exact h.input
  · rw [a.output, a.keeps.wr]; exact h.outputWrite
  · rw [a.work, a.keeps.wr]; exact h.workWrite
  · rw [a.input, a.work]; exact h.inputWork
  · rw [a.output, a.work]; exact h.outputWork
  · rw [a.input, sp]; exact h.stackInput
  · rw [a.output, sp]; exact h.stackOutput
  · rw [a.work, sp]; exact h.stackWork

end VG.Proof.Argon2.X86_64.FinalOutput

end

end

/-! Merged from `Proof.Argon2.X86_64.ReduceLanesBody`. -/

@[expose] public section

section
/-! One reduction iteration advances a public lane and preserves the accumulator invariant. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (lane : Nat) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  active : lane < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  laneWord : s.gpr .rbx = BitVec.ofNat 64 lane
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

structure Done (s t : State) (p : Params) (lane : Nat) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 (lane + 1)
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  cf : t.cf = decide (lane + 1 < p.lanes)
  next : lane + 1 < p.lanes → Ready p (lane + 1) t

theorem body_ok (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.X86_64.ReduceLanes.body s
      (Done s · p lane memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
  unfold Impl.Argon2.X86_64.ReduceLanes.body Impl.Argon2.X86_64.ReduceLanes.advance
  refine WP.seq ((ReduceLane.code_ok s p lane h.allocation h.active h.laneWord memory acc represented).mono ?_)
  intro a reduced
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 184) 8 := by
    rw [reduced.rd, reduced.wr, reduced.regs .rbp (by simp [calleeSaved])]; exact h.lanesRead
  have word := (ReductionState.frame_word h.allocation reduced 184 (by decide)).trans h.lanesWord
  refine (FillLanes.advance_ok a read).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : matrix t = matrix a := by unfold matrix; rw [keeps.mem, bp]
  have added : a.gpr .rbx + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [reduced.regs .rbx (by simp [calleeSaved]), h.laneWord, BitVec.ofNat_add]; rfl
  have nextWord := value.trans added
  refine ⟨reduced.represented.of_state bp keeps.mem, base.trans reduced.base, nextWord,
    ?_, keeps.rd.trans reduced.rd, keeps.wr.trans reduced.wr, ?_, keeps.mxcsr.trans reduced.mxcsr, ?_, ?_⟩
  · intro r hr bx
    exact (keeps.regs r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using bx)).trans (reduced.regs r hr)
  · rw [keeps.mem]; exact reduced.frame
  · rw [flag, added, word, ReferenceMap.word_nat (lane + 1) (by have bound := h.lanesBound; have active := h.active; omega_using [bound, active]),
      ReferenceMap.word_nat p.lanes (Nat.lt_trans h.lanesBound (by decide))]
  · intro active
    refine ⟨reduced.ready.of_state bp (keeps.regs .r12 (by decide)) keeps.mem keeps.rd keeps.wr,
      active, h.lanesBound, nextWord, ?_, ?_⟩
    · rw [keeps.rd, keeps.wr, bp]; exact read
    · rw [keeps.mem, bp]; exact word

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Merged from `Proof.Argon2.X86_64.ReductionInit`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReductionClear`. -/
section
/-! Clear only block zero, preserving the original last blocks in the matrix. -/

namespace VG.Proof.Argon2.X86_64.ReductionState

open VG VG.X86_64 VG.Spec.Argon2

structure Cleared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : Ready p t
  represented : Represents p memory zeroBlock t
  base : matrix t = matrix s
  keeps : CopyKeeps s t
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem clear_ok (s : State) (p : Params) (h : Ready p s)
    (dest : s.gpr .rdi = matrix s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.ClearBlock.code s (Cleared s · p memory) := by
  have write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr := by rw [dest]; exact h.accumulator_cover
  refine (ClearBlock.code_ok s write).mono ?_
  rintro t ⟨zero, frame, keeps, mx⟩
  rw [dest] at frame zero
  have bp := keeps.1 .rbp (by decide)
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  have metadata (d : Nat) (bound : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bp]
    exact frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact h.frame.symm.sub_right (Region.sub_prefix (by omega_using [nonempty]))) (by decide)
  have base : matrix t = matrix s := metadata 232 (by decide)
  refine ⟨?_, ?_, base, keeps, frame, mx⟩
  · refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (keeps.1 .r12 (by decide)).trans h.length⟩
    · rw [keeps.2.1, keeps.2.2, bp]; exact h.read
    · rw [base, keeps.2.2]; exact h.write
    · rw [base, bp]; exact h.frame
  · constructor
    · rw [base]; exact zero
    · intro lane active
      rw [base]
      apply Eq.trans _ (represented.block _ (Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active).2)
      apply FillCompress.block_frame frame
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      have bounds := Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active
      simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
        Proof.Argon2.matrixCell_disjoint (matrix s) p.blocks (Proof.Argon2.lastIndex p lane) 0 h.bound
          bounds.2 (by omega_using [nonempty]) (by omega_using [bounds])

theorem Cleared.frame_word {p : Params} {s t : State} {memory : Array Block}
    (ready : Ready p s) (done : Cleared s t p memory) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.keeps.1 .rbp (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.positive ready.minimum 0 ready.positive
          omega_using [nonempty]))) (by decide)

end VG.Proof.Argon2.X86_64.ReductionState
end

/-! Merged from `Proof.Argon2.X86_64.ReduceLanes`. -/
section
/-! Termination and correctness of the final lane reduction. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Finished (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc : Block}
    (h : Done s t p lane memory acc) (last : lane + 1 = p.lanes) : Finished s t p memory acc :=
  ⟨h.represented, h.base, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc result : Block}
    (first : Done s a p lane memory acc) (rest : Finished a t p memory result) : Finished s t p memory result := by
  refine ⟨rest.represented, rest.base.trans first.base, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [first.base] at frame
    exact first.frame.trans frame
  · intro r hr bx; exact (rest.regs r hr bx).trans (first.regs r hr bx)

theorem loop_ok (count : Nat) (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.X86_64.ReduceLanes.loop s
      (Finished s · p memory (Proof.Argon2.reduction p memory lane count acc)) := by
  induction count generalizing s lane acc with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p lane h memory acc represented
    rw [Proof.Argon2.reduction_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega_using [endLane]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active) _
        done.represented (by omega_using []) (by omega_using [endLane])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Establish the invariant for reducing all lanes, retaining the input matrix's last blocks. -/

namespace VG.Proof.Argon2.X86_64.ReductionInit

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  lanesBound : p.lanes < 2 ^ 32
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 232) 8) :
    WP isa (.block Impl.Argon2.X86_64.ReductionInit.setup) s fun t =>
      t.gpr .rdi = matrix s ∧ t.gpr .rbx = 0 ∧ Divide.Keeps [.rdi, .rbx] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ReductionInit.setup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_at, read, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg, reduceCtorEq, ite_false]
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

structure Prepared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : ReduceLanes.Ready p 0 t
  represented : ReductionState.Represents p memory zeroBlock t
  base : matrix t = matrix s
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem code_ok (s : State) (p : Params) (h : Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.ReductionInit.code s (Prepared s · p memory) := by
  unfold Impl.Argon2.X86_64.ReductionInit.code
  refine WP.seq ((setup_ok s h.allocation.read).mono ?_)
  rintro a ⟨dest, lane, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : matrix a = matrix s := by unfold matrix; rw [keeps.mem, bp]
  have ha := h.allocation.of_state bp (keeps.regs .r12 (by decide)) keeps.mem keeps.rd keeps.wr
  have rep : Proof.Argon2.Represents a.mem (matrix a) p.blocks memory := by rw [keeps.mem, base]; exact represented
  refine (ReductionState.clear_ok a p ha (dest.trans base.symm) memory rep).mono ?_
  intro t cleared
  refine ⟨⟨cleared.ready, ha.positive, h.lanesBound,
    (cleared.keeps.1 .rbx (by decide)).trans lane, ?_, ?_⟩,
    cleared.represented, cleared.base.trans base, ?_, cleared.keeps.2.1.trans keeps.rd,
    cleared.keeps.2.2.trans keeps.wr, ?_, cleared.mxcsr.trans keeps.mxcsr⟩
  · rw [cleared.keeps.2.1, cleared.keeps.2.2, cleared.keeps.1 .rbp (by decide), keeps.rd, keeps.wr, bp]
    exact h.lanesRead
  · rw [cleared.frame_word ha 184 (by decide), keeps.mem, bp]; exact h.lanesWord
  · intro r hr bx
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have notDest : r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (cleared.keeps.1 r ne).trans (keeps.regs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨notDest, bx⟩))
  · have frame := cleared.frame
    rw [base, keeps.mem] at frame; exact frame

end VG.Proof.Argon2.X86_64.ReductionInit
end

/-! Merged from `Proof.Argon2.X86_64.ReductionInitCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReducePointersCT`. -/
section
/-! Pointer preparation reads one public frame location and performs fixed arithmetic. -/

namespace VG.Proof.Argon2.X86_64.ReducePointers

open VG VG.X86_64

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    Impl.Argon2.X86_64.ReducePointers.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.ReducePointers
end

/-! Merged from `Proof.Argon2.X86_64.ReduceLanesCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceLanesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceLaneCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceBlockCT`. -/
section
/-! Final block XOR has fixed accesses determined only by its public pointers. -/

namespace VG.Proof.Argon2.X86_64.ReduceBlock

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReduceBlock

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rdi, .rsi], s.gpr r = t.gpr r) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64.ReduceBlock
end

/-! Final lane reduction depends only on public lane coordinates and matrix pointers. -/

namespace VG.Proof.Argon2.X86_64.ReduceLane

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  active : lane < p.lanes
  leftLane : s.gpr .rbx = BitVec.ofNat 64 lane
  rightLane : t.gpr .rbx = BitVec.ofNat 64 lane
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t

theorem pointers_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.X86_64.ReducePointers.code
      (fun s t => ∀ r ∈ [Reg.rdi, .rsi], s.gpr r = t.gpr r) := by
  have trace := ReducePointers.code_rel.mono (P' := Related p lane) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => by
    have q : 0 < p.laneLen := by
      have eq := Proof.Argon2.laneLen_segments p h.left.positive
      have minimum := h.left.minimum
      omega_using [eq, minimum]
    exact ⟨ReducePointers.code_ok s lane p.laneLen q h.left.read h.leftLane h.left.length,
      ReducePointers.code_ok t lane p.laneLen q h.right.read h.rightLane h.right.length⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨destA, srcA, _⟩, ⟨destB, srcB, _⟩⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact destA.trans (hp.matrices.trans destB.symm)
  · have bases : s.mem.readW (off (s.gpr .rbp) 232) 64 = t.mem.readW (off (t.gpr .rbp) 232) 64 := hp.matrices
    rw [srcA, srcB, bases]

theorem code_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.X86_64.ReduceLane.code (fun _ _ => True) :=
  (pointers_rel p lane).seq ReduceBlock.code_rel

end VG.Proof.Argon2.X86_64.ReduceLane
end

/-! Reduction visits the same last blocks even when their contents differ. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (s t : State) : Prop where
  left : Ready p lane s
  right : Ready p lane t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t
  leftRep : ReductionState.Represents p leftMemory leftAcc s
  rightRep : ReductionState.Represents p rightMemory rightAcc t

theorem advance_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.ReduceLanes.advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem body_rel (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.X86_64.ReduceLanes.body
      (fun s t => s.cf = t.cf ∧ (lane + 1 < p.lanes → Related p (lane + 1) leftMemory rightMemory
        (xorBlock leftAcc (leftMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))
        (xorBlock rightAcc (rightMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock)) s t)) := by
  intro s t ts tt a b hp ea eb
  have related : ReduceLane.Related p lane s t :=
    ⟨hp.left.allocation, hp.right.allocation, hp.left.active, hp.left.laneWord, hp.right.laneWord, hp.bases, hp.matrices⟩
  cases ea with
  | seq reduceA advanceA =>
    cases eb with
    | seq reduceB advanceB =>
      obtain ⟨reduceTrace, _⟩ := ReduceLane.code_rel p lane _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, reducedA⟩ := ReduceLane.code_ok s p lane hp.left.allocation hp.left.active
        hp.left.laneWord leftMemory leftAcc hp.leftRep
      obtain ⟨_, sb, runB, reducedB⟩ := ReduceLane.code_ok t p lane hp.right.allocation hp.right.active
        hp.right.laneWord rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have bases := (reducedA.regs .rbp (by simp [calleeSaved])).trans
        (hp.bases.trans (reducedB.regs .rbp (by simp [calleeSaved])).symm)
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p lane hp.left leftMemory leftAcc hp.leftRep
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p lane hp.right rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceB advanceB) runB
      refine ⟨by rw [reduceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_,
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! The final reduction leaks only public matrix addresses and the public lane count. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2

theorem loop_rel (p : Params) (lane count : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.X86_64.ReduceLanes.loop
      (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftAcc rightAcc : Block), lane + n = p.lanes ∧ 0 < n ∧
    Related p lane leftMemory rightMemory leftAcc rightAcc s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.ReduceLanes.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, la, ra, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨trace, flags, next⟩ := body_rel p j leftMemory rightMemory la ra _ _ _ _ _ _ hp ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p j hp.left leftMemory la hp.leftRep
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        exact ⟨n, by omega_using [], j + 1, _, _, by omega_using [endLane], by omega_using [endLane, active], next active⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftAcc, rightAcc, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Clearing the accumulator follows public pointers and visits a fixed block. -/

namespace VG.Proof.Argon2.X86_64.ReductionInit

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem setup_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.ReductionInit.setup) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem clear_rel : RelCT isa (fun s t => s.gpr .rdi = t.gpr .rdi)
    Impl.Argon2.X86_64.ClearBlock.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem code_rel (p : Params) (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) Impl.Argon2.X86_64.ReductionInit.code
      (ReduceLanes.Related p 0 leftMemory rightMemory zeroBlock zeroBlock) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA clearA =>
    cases eb with
    | seq setupB clearB =>
      obtain ⟨setupTrace, _⟩ := setup_rel _ _ _ _ _ _ hp.bases setupA setupB
      obtain ⟨_, sa, runA, destA, _, _⟩ := setup_ok s hp.left.allocation.read
      obtain ⟨_, sb, runB, destB, _, _⟩ := setup_ok t hp.right.allocation.read
      obtain ⟨_, rfl⟩ := Exec.det setupA runA
      obtain ⟨_, rfl⟩ := Exec.det setupB runB
      obtain ⟨clearTrace, _⟩ := clear_rel _ _ _ _ _ _ (destA.trans (hp.matrices.trans destB.symm)) clearA clearB
      obtain ⟨_, a', runA, doneA⟩ := code_ok s p hp.left leftMemory hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := code_ok t p hp.right rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupA clearA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupB clearB) runB
      refine ⟨by rw [setupTrace, clearTrace], doneA.ready, doneB.ready, ?_,
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReductionInit
end

/-! Merged from `Proof.Argon2.X86_64.FinalReduction`. -/
section
/-! Complete final block reduction, including setup, termination and a public trace. -/

namespace VG.Proof.Argon2.X86_64.FinalReduction

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

theorem code_ok (s : State) (p : Params) (h : ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.FinalReduction.code s
      (ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock)) := by
  unfold Impl.Argon2.X86_64.FinalReduction.code
  refine WP.seq ((ReductionInit.code_ok s p h memory represented).mono ?_)
  intro a prepared
  refine (ReduceLanes.loop_ok p.lanes a p 0 prepared.ready memory zeroBlock prepared.represented
    h.allocation.positive (Nat.zero_add _)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.base.trans prepared.base, finished.laneWord,
    finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.mxcsr.trans prepared.mxcsr, ?_⟩
  · have frame := finished.frame
    rw [prepared.base] at frame
    exact prepared.frame.trans frame
  · intro r hr bx; exact (finished.regs r hr bx).trans (prepared.regs r hr bx)

theorem code_rel (p : Params) (positive : 0 < p.lanes) (leftMemory rightMemory : Array Block) :
    RelCT isa (ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.X86_64.FinalReduction.code
      (fun _ _ => True) :=
  (ReductionInit.code_rel p leftMemory rightMemory).seq
    (ReduceLanes.loop_rel p 0 p.lanes leftMemory rightMemory zeroBlock zeroBlock positive (Nat.zero_add _))

end VG.Proof.Argon2.X86_64.FinalReduction
end

/-! Preserve the final-call allocations and metadata through the matrix reduction. -/

namespace VG.Proof.Argon2.X86_64.Finish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  reduction : ReductionInit.Ready p s
  output : FinalOutput.Ready p s

theorem frame_word {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : ReductionInit.Ready p s) (done : ReduceLanes.Finished s t p memory acc)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved]) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega_using [bound]))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.allocation.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.allocation.positive ready.allocation.minimum 0 ready.allocation.positive
          omega_using [nonempty]))) (by decide)

theorem output_ready {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : Ready p s) (done : ReduceLanes.Finished s t p memory acc) : FinalOutput.Ready p t := by
  have bp := done.regs .rbp (by simp [calleeSaved]) (by decide)
  have sp := done.regs .rsp (by simp [calleeSaved]) (by decide)
  have output : FinalOutput.output t = FinalOutput.output s := frame_word ready.reduction done 256 (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := frame_word ready.reduction done 248 (by decide)
  refine ⟨ready.output.positive, ready.output.bound, ?_,
    (frame_word ready.reduction done 264 (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, bp]; exact ready.output.reads
  · rw [done.base, done.rd, done.wr]; exact ready.output.input
  · rw [output, done.wr]; exact ready.output.outputWrite
  · rw [work, done.wr]; exact ready.output.workWrite
  · rw [done.base, work]; exact ready.output.inputWork
  · rw [output, work]; exact ready.output.outputWork
  · rw [sp, done.base]; exact ready.output.stackInput
  · rw [sp, output]; exact ready.output.stackOutput
  · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.X86_64.Finish

end

end

/-! ### `Argon2.X86_64.FillIterations`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillIterationsBody`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillIteration`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillSlices`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillSlicesBody`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillSlice`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillLanes`, which only this module used -/

section

/-! ### `Argon2.X86_64.FillLanesBody`, which only this module used -/

section

/-! One lane iteration fills its segment and advances the public lane. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 (lane + 1)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r15 → t.gpr r = s.gpr r
  header : ∃ a, SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.rbx] a t
  cf : t.cf = decide (lane + 1 < p.lanes)
  next : lane + 1 < p.lanes → SegmentSetup.Ready p pass (lane + 1) slice t

theorem body_ok [CompressImpl] (s : State) (p : Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillLanes.body s (Done s · p pass lane slice state) := by
  unfold Impl.Argon2.X86_64.FillLanes.body
  refine WP.seq ((SegmentSetup.code_ok s p pass lane slice h state represented).mono ?_)
  intro a filled
  have ready := finished_ready h.parameters filled
  refine (advance_ok a (ready.layout.frameRead 184 (by simp))).mono ?_
  rintro t ⟨value, flag, keeps⟩
  obtain ⟨old, words⟩ := ready.words
  have bp := keeps.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  have added : a.gpr .rbx + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [words.laneWord, BitVec.ofNat_add]; rfl
  have nextWord := value.trans added
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans h.parameters.lanesBound (by decide)
  have laneBound := h.parameters.laneBound
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextWord, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, (ctl_eq_of keeps.mxcsr).trans filled.mxcsr, ?_, ⟨a, ready, keeps⟩, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx ix
    have outside : r ∉ [Reg.rbx] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact bx
    exact (keeps.regs r outside).trans (filled.regs r hr ix)
  · rw [flag, added, ready.lanesWord, ReferenceMap.word_nat (lane + 1) (by omega_using [lanesBound, laneBound]),
      ReferenceMap.word_nat p.lanes lanesBound]
  · intro active; exact change_lane_ready ready keeps nextWord active

end VG.Proof.Argon2.X86_64.FillLanes

end

end


/-! Termination and correctness of all remaining lanes in one slice. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r15 → t.gpr r = s.gpr r
  header : ∃ lane a, lane + 1 = p.lanes ∧ SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.rbx] a t

theorem Done.finished {s t : State} {p : Params} {pass lane slice : Nat} {state : FillState}
    (h : Done s t p pass lane slice state) (last : lane + 1 = p.lanes) :
    Finished s t p pass slice (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) := by
  obtain ⟨a, ready, keeps⟩ := h.header
  exact ⟨h.represented, h.matrix, h.work, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.mxcsr,
    h.regs, lane, a, last, ready, keeps⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice : Nat} {state finalState : FillState}
    (first : Done s a p pass lane slice state) (rest : Finished a t p pass slice finalState) :
    Finished s t p pass slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_, rest.header⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx ix; exact (rest.regs r hr bx ix).trans (first.regs r hr bx ix)

theorem loop_ok [CompressImpl] (count : Nat) (s : State) (p : Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.X86_64.FillLanes.loop s
      (Finished s · p pass slice (Proof.Argon2.lanes p pass slice lane count state)) := by
  induction count generalizing s lane state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass lane slice h state represented
    rw [Proof.Argon2.lanes_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega_using [endLane]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) done.represented (by omega_using []) (by omega_using [endLane])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.FillLanes

end

end


/-! Merged from `Proof.Argon2.X86_64.FillSlicePrepare`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.X86_64.FillHeader`. -/
section
/-! Allocation and normalized header across lane, slice and pass boundaries. -/

namespace VG.Proof.Argon2.X86_64.FillHeader

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .r12 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem of_segment_ready {p : Params} {pass lane slice : Nat} {s : State}
    (h : SegmentSetup.Ready p pass lane slice s) : Ready p pass lane slice s :=
  ⟨h.layout, h.addressLayout, h.reads, h.write, h.words, h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.segment {p : Params} {pass lane slice : Nat} {s : State}
    (h : Ready p pass lane slice s) (parameters : FillContext.Parameters p pass lane slice) :
    SegmentSetup.Ready p pass lane slice s :=
  ⟨parameters, h.layout, h.addressLayout, h.reads, h.write, h.words,
    h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.of_state {p : Params} {pass lane slice newLane newSlice : Nat} {s t : State}
    (h : Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.rbp, .rsp, .r12, .r13], t.gpr r = s.gpr r)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (laneWord : t.gpr .rbx = BitVec.ofNat 64 newLane) (sliceWord : t.gpr .r14 = BitVec.ofNat 64 newSlice) :
    Ready p pass newLane newSlice t := by
  have bp := regs .rbp (by simp)
  have sp := regs .rsp (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .r12 (by simp)).trans h.laneLength, (regs .r13 (by simp)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, laneWord, sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem of_lanes_finished {p : Params} {pass slice : Nat} {s t : State} {state : FillState}
    (h : FillLanes.Finished s t p pass slice state) : Ready p pass p.lanes slice t := by
  obtain ⟨lane, a, _, ready, keeps⟩ := h.header
  obtain ⟨old, words⟩ := ready.words
  apply (of_segment_ready ready).of_state _ keeps.mem keeps.rd keeps.wr h.laneWord
    ((keeps.regs .r14 (by decide)).trans words.sliceWord)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)

end VG.Proof.Argon2.X86_64.FillHeader
end

/-! Initialize lane zero without requiring a valid incoming lane coordinate. -/

namespace VG.Proof.Argon2.X86_64.FillSlice

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (pass slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 slice
  header : ∃ lane, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass slice : Nat) : Prop where
  ready : SegmentSetup.Ready p pass 0 slice t
  keeps : Divide.Keeps [.rbx] s t

theorem setup_ok (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) :
    WP isa (.block Impl.Argon2.X86_64.FillSlice.setup) s (Prepared s · p pass slice) := by
  refine (SegmentSetup.register_ok s .rbx 0).mono ?_
  rintro t ⟨laneWord, keeps⟩
  obtain ⟨lane, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass 0 slice t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.mem keeps.rd keeps.wr laneWord ((keeps.regs .r14 (by decide)).trans words.sliceWord)
  exact ⟨next.segment h.parameters, keeps⟩

end VG.Proof.Argon2.X86_64.FillSlice
end

/-! Correctness of one complete slice, starting at lane zero. -/

namespace VG.Proof.Argon2.X86_64.FillSlice

open VG VG.X86_64 VG.Spec.Argon2

theorem code_ok [CompressImpl] (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSlice.code s
      (FillLanes.Finished s · p pass slice (Proof.Argon2.lanes p pass slice 0 p.lanes state)) := by
  unfold Impl.Argon2.X86_64.FillSlice.code
  refine WP.seq ((setup_ok s p pass slice h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .rbp (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillLanes.loop_ok p.lanes a p pass 0 slice prepared.ready state representedA
    h.parameters.lanesPositive (by omega_using [])).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.laneWord,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.mxcsr.trans (ctl_eq_of prepared.keeps.mxcsr), ?_, finished.header⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.regs .rsp (by decide), bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx ix
    have ne : r ∉ [Reg.rbx] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact bx
    exact (finished.regs r hr bx ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.X86_64.FillSlice

end

end


/-! Merged from `Proof.Argon2.X86_64.FillSliceAdvance`. -/

@[expose] public section

section
/-! Slice advancement retains the public header and matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSlices

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    t.gpr .r14 = s.gpr .r14 + 1 ∧ t.cf = decide ((s.gpr .r14 + 1).toNat < 4) ∧ Divide.Keeps [.r14] s t := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (4 : BitVec 32) = (4 : Addr) from rfl,
    show (4 : Addr).toNat = 4 from rfl,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem advanced_header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : FillHeader.Ready p pass lane slice s) (k : Divide.Keeps [.r14] s t)
    (value : t.gpr .r14 = BitVec.ofNat 64 (slice + 1)) : FillHeader.Ready p pass lane (slice + 1) t := by
  obtain ⟨old, words⟩ := h.words
  exact h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide))
    k.mem k.rd k.wr ((k.regs .rbx (by decide)).trans words.laneWord) value

end VG.Proof.Argon2.X86_64.FillSlices
end

/-! Fill one slice and advance its public coordinate. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.lanes p pass slice 0 p.lanes state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes (slice + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  cf : t.cf = decide (slice + 1 < 4)
  next : slice + 1 < 4 → FillSlice.Ready p pass (slice + 1) t

theorem body_ok [CompressImpl] (s : State) (p : Params) (pass slice : Nat) (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSlices.body s (Done s · p pass slice state) := by
  unfold Impl.Argon2.X86_64.FillSlices.body
  refine WP.seq ((FillSlice.code_ok s p pass slice h state represented).mono ?_)
  intro a filled
  have header := FillHeader.of_lanes_finished filled
  obtain ⟨old, words⟩ := header.words
  refine (advance_ok a).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have added : a.gpr .r14 + 1 = BitVec.ofNat 64 (slice + 1) := by
    rw [words.sliceWord, BitVec.ofNat_add]; rfl
  have nextWord := value.trans added
  have nextHeader := advanced_header header keeps nextWord
  have bp := keeps.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  have sliceBound := h.parameters.sliceBound
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextHeader, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, (ctl_eq_of keeps.mxcsr).trans filled.mxcsr, ?_, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx sl ix
    have outside : r ∉ [Reg.r14] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (keeps.regs r outside).trans (filled.regs r hr bx ix)
  · rw [flag, added, ReferenceMap.word_nat (slice + 1) (by omega_using [sliceBound])]
  · intro active
    exact ⟨{ h.parameters with sliceBound := active }, p.lanes, nextHeader⟩

end VG.Proof.Argon2.X86_64.FillSlices

end

end


/-! Termination and correctness of the four-slice filling pass. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass slice : Nat} {state : FillState}
    (h : Done s t p pass slice state) (last : slice + 1 = 4) :
    Finished s t p pass (Proof.Argon2.lanes p pass slice 0 p.lanes state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass slice : Nat} {state finalState : FillState}
    (first : Done s a p pass slice state) (rest : Finished a t p pass finalState) : Finished s t p pass finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok [CompressImpl] (count : Nat) (s : State) (p : Params) (pass slice : Nat)
    (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    WP isa Impl.Argon2.X86_64.FillSlices.loop s (Finished s · p pass (Proof.Argon2.slices p pass slice count state)) := by
  induction count generalizing s slice state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass slice h state represented
    rw [Proof.Argon2.slices_succ]
    cases n with
    | zero =>
      have last : slice + 1 = 4 := endSlice
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : slice + 1 < 4 := by omega_using [endSlice]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (slice + 1) (done.next active)
        (Proof.Argon2.lanes p pass slice 0 p.lanes state) done.represented (by omega_using []) (by omega_using [endSlice])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

theorem pass_ok [CompressImpl] (s : State) (p : Params) (pass : Nat) (h : FillSlice.Ready p pass 0 s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSlices.loop s (Finished s · p pass (fillPass p state pass)) := by
  rw [← Proof.Argon2.slices_pass p pass state]
  exact loop_ok 4 s p pass 0 h state represented (by decide) (by decide)

end VG.Proof.Argon2.X86_64.FillSlices

end

end


/-! Merged from `Proof.Argon2.X86_64.FillIterationPrepare`. -/

@[expose] public section

section
/-! Start a pass at slice zero regardless of its incoming lane and slice coordinates. -/

namespace VG.Proof.Argon2.X86_64.FillIteration

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 0
  header : ∃ lane slice, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass : Nat) : Prop where
  ready : FillSlice.Ready p pass 0 t
  keeps : Divide.Keeps [.r14] s t

theorem setup_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) :
    WP isa (.block Impl.Argon2.X86_64.FillIteration.setup) s (Prepared s · p pass) := by
  refine (SegmentSetup.register_ok s .r14 0).mono ?_
  rintro t ⟨sliceWord, keeps⟩
  obtain ⟨lane, slice, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass lane 0 t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.mem keeps.rd keeps.wr ((keeps.regs .rbx (by decide)).trans words.laneWord) sliceWord
  exact ⟨⟨h.parameters, lane, next⟩, keeps⟩

end VG.Proof.Argon2.X86_64.FillIteration
end

/-! One complete filling pass against the reviewed specification. -/

namespace VG.Proof.Argon2.X86_64.FillIteration

open VG VG.X86_64 VG.Spec.Argon2

theorem code_ok [CompressImpl] (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillIteration.code s (FillSlices.Finished s · p pass (fillPass p state pass)) := by
  unfold Impl.Argon2.X86_64.FillIteration.code
  refine WP.seq ((setup_ok s p pass h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .rbp (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillSlices.pass_ok a p pass prepared.ready state representedA).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.header,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.mxcsr.trans (ctl_eq_of prepared.keeps.mxcsr), ?_⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.regs .rsp (by decide), bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.r14] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (finished.regs r hr bx sl ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.X86_64.FillIteration

end

end


/-! Merged from `Proof.Argon2.X86_64.FillPassSave`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.X86_64.FillPassCounter`. -/
section
/-! Increment, save and compare the public pass counter. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

theorem increment_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block increment) s fun t =>
      t.gpr .rax = s.mem.readW (off (s.gpr .rbp) 0) 64 + 1 ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [increment, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem saveCheck_ok (s : State) (hw : InRegions s.wr (off (s.gpr .rbp) 0) 8)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 72) 8) :
    WP isa (.block saveCheck) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      t.cf = decide ((s.gpr .rax).toNat < (s.mem.readW (off (s.gpr .rbp) 72) 64).toNat) := by
  apply WP.of_runBlock
  have sep : Mem.Sep (off (s.gpr .rbp) 72) 8 (off (s.gpr .rbp) 0) 8 :=
    Offset.sep _ (by decide) (by decide) (by decide)
  simp only [saveCheck, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    State.load64, ea_at, hw, hr, readSrc, execAlu, ite_true,
    Mem.readW_writeW_sep (w := 64) (w' := 64) sep (by decide), RegUpd.cf_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.gpr_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, trivial⟩
  rfl

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! A saved pass counter changes only its eight-byte header word. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (s.mem.readW (off (s.gpr .rbp) 0) 64 + 1)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  cf : t.cf = decide ((s.mem.readW (off (s.gpr .rbp) 0) 64 + 1).toNat <
    (s.mem.readW (off (s.gpr .rbp) 72) 64).toNat)
  frame : Frame [⟨off (s.gpr .rbp) 0, 8⟩] s.mem t.mem

theorem advance_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8)
    (write : InRegions s.wr (off (s.gpr .rbp) 0) 8)
    (passesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 72) 8) : WP isa advance s (Saved s) := by
  unfold advance
  refine WP.seq ((increment_ok s read).mono ?_)
  rintro a ⟨value, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have readA : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 72) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact passesRead
  have writeA : InRegions a.wr (off (a.gpr .rbp) 0) 8 := by rw [keeps.wr, bp]; exact write
  refine (saveCheck_ok a writeA readA).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx, cf⟩
  have finalMem : t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (s.mem.readW (off (s.gpr .rbp) 0) 64 + 1) := by
    rw [mem, keeps.mem, bp, value]
  refine ⟨finalMem, ?_, rd.trans keeps.rd, wr.trans keeps.wr, ctl_eq_of (mx.trans keeps.mxcsr), ?_, ?_⟩
  · intro r ne
    have outside : r ∉ [Reg.rax] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ne
    exact (congrFun regs r).trans (keeps.regs r outside)
  · rw [cf, value, keeps.mem, bp]
  · rw [finalMem]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 0, 8⟩) (by simp) _ (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs .rbp (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8)
    (by omega_using [separate]) (by omega_using [bound]) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s) :
    AddressHeader.Words p (pass + 1) lane slice old t := by
  refine ⟨?_, (h.regs .rbx (by decide)).trans words.laneWord,
    (h.regs .r14 (by decide)).trans words.sliceWord,
    (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord,
    (h.read 8 (by decide) (by decide)).trans words.counterWord⟩
  rw [h.regs .rbp (by decide), h.mem, Mem.readW_writeW_self64, words.passWord, BitVec.ofNat_add]
  rfl

theorem Saved.header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) : FillHeader.Ready p (pass + 1) lane slice t := by
  have bp := h.regs .rbp (by decide)
  have sp := h.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := h.read 248 (by decide) (by decide)
  refine ⟨header.layout.of_preserved bp sp base work h.rd h.wr, ?_, ?_, ?_, ?_, ?_,
    (h.regs .r12 (by decide)).trans header.laneLength, (h.regs .r13 (by decide)).trans header.segmentLength, ?_⟩
  · constructor
    · rw [h.rd, h.wr, bp]; exact header.addressLayout.frameRead
    · rw [h.wr, work]; exact header.addressLayout.workWrite
    · rw [bp, work]; exact header.addressLayout.frameWork
    · rw [bp, sp]; exact header.addressLayout.frameStack
    · rw [sp, work]; exact header.addressLayout.stackWork
  · rw [h.rd, h.wr, bp]; exact header.reads
  · rw [h.wr, bp]; exact header.write
  · obtain ⟨old, words⟩ := header.words; exact ⟨old, h.words words⟩
  · rw [base, work]; exact header.matrixWork
  · exact (h.read 184 (by decide) (by decide)).trans header.lanesWord

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! Merged from `Proof.Argon2.X86_64.FillIterationsFrame`. -/
section
/-! The outer pass loop also writes the public pass word at frame offset zero. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below (s.gpr .rsp) 8, ⟨s.gpr .rbp, 24⟩]

theorem filling_frame {s t : State} {p : Params} (h : Frame (FillBlock.writes s p) s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillBlock.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .rbp, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.outer_frame {s t : State} {p : Params} (h : Saved s t) : Frame (writes s p) s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .rbp, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.represents {s t : State} {p : Params} {pass lane slice : Nat}
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  rw [base]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (header.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! A complete pass retains the matrix and advances its public iteration counter. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  filling : FillIteration.Ready p pass s
  passesBound : p.passes < 2 ^ 32
  passWrite : InRegions s.wr (off (s.gpr .rbp) 0) 8

structure Done (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks (fillPass p state pass).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p (pass + 1) p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  cf : t.cf = decide (pass + 1 < p.passes)
  next : pass + 1 < p.passes → Ready p (pass + 1) t

theorem body_ok [CompressImpl] (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillIterations.body s (Done s · p pass state) := by
  unfold Impl.Argon2.X86_64.FillIterations.body
  refine WP.seq ((FillIteration.code_ok s p pass h.filling state represented).mono ?_)
  intro a filled
  have write : InRegions a.wr (off (a.gpr .rbp) 0) 8 := by
    rw [filled.wr, filled.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)]
    exact h.passWrite
  refine (advance_ok a (filled.header.reads 0 (by simp)) write (filled.header.reads 72 (by simp))).mono ?_
  intro t saved
  have header := saved.header filled.header
  obtain ⟨old, words⟩ := filled.header.words
  have base : FillKernel.matrix t = FillKernel.matrix a := saved.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work a := saved.read 248 (by decide) (by decide)
  have passBound := h.filling.parameters.passBound
  refine ⟨saved.represents filled.header _ filled.represented, base.trans filled.matrix,
    work.trans filled.work, header, saved.rd.trans filled.rd, saved.wr.trans filled.wr,
    ?_, saved.mxcsr.trans filled.mxcsr, ?_, ?_, ?_⟩
  · have lastFrame := saved.outer_frame (p := p)
    rw [writes, filled.matrix, filled.work,
      filled.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide),
      filled.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at lastFrame
    exact (filling_frame filled.frame).trans lastFrame
  · intro r hr bx sl ix
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (saved.regs r ne).trans (filled.regs r hr bx sl ix)
  · have added : (BitVec.ofNat 64 pass + 1 : Addr) = BitVec.ofNat 64 (pass + 1) := by
      rw [BitVec.ofNat_add]; rfl
    rw [saved.cf, words.passWord, words.passesWord, added, ReferenceMap.word_nat (pass + 1) (by omega_using [passBound]),
      ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
  · intro active
    refine ⟨⟨{ h.filling.parameters with passBound := Nat.lt_trans active h.passesBound }, p.lanes, 4, header⟩,
      h.passesBound, ?_⟩
    rw [saved.wr, saved.regs .rbp (by decide)]; exact write

end VG.Proof.Argon2.X86_64.FillIterations

end

end


/-! Termination and correctness of every requested filling pass. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p p.passes p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (h : Done s t p pass state) (last : pass + 1 = p.passes) : Finished s t p (fillPass p state pass) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass : Nat} {state finalState : FillState}
    (first : Done s a p pass state) (rest : Finished a t p finalState) : Finished s t p finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok [CompressImpl] (count : Nat) (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    WP isa Impl.Argon2.X86_64.FillIterations.loop s (Finished s · p (Proof.Argon2.iterations p pass count state)) := by
  induction count generalizing s pass state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass h state represented
    rw [Proof.Argon2.iterations_succ]
    cases n with
    | zero =>
      have last : pass + 1 = p.passes := endPass
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : pass + 1 < p.passes := by omega_using [endPass]
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (pass + 1) (done.next active)
        (fillPass p state pass) done.represented (by omega_using []) (by omega_using [endPass])
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

theorem Finished.frame_word {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (ready : Ready p pass s) (done : Finished s t p state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : 24 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)]
  obtain ⟨lane, slice, header⟩ := ready.filling.header
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact header.layout.matrixFrame.symm.sub_left sub
    · exact header.addressLayout.frameWork.sub_left sub
    · exact header.addressLayout.frameStack.sub_left sub
    · simpa only [off, BitVec.add_zero] using Offset.disjoint (d := d) (n := 8) (e := 0) (k := 24) (s.gpr .rbp) (Or.inr (by omega_using [separate])) (by omega_using [bound]) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.FillIterations

end

end


/-! Merged from `Proof.Argon2.X86_64.FinishStage`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.X86_64.FinalOutput`. -/
section
/-! The generic H′ call produces exactly the reviewed final Argon2 tag. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (output s) p.tagLen = finish p memory
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨output s, p.tagLen⟩, ⟨work s, 16384⟩, below (s.gpr .rsp) 24] s.mem t.mem

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (block : blockAt s.mem (ReductionState.matrix s) = Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) :
    WP isa (Impl.Argon2.X86_64.FinalOutput.code name (HPrime.hash v)) s (Done s · p memory) := by
  unfold Impl.Argon2.X86_64.FinalOutput.code
  refine WP.seq ((args_ok s h.reads).mono ?_)
  intro a args
  have length := args.outputLength.trans h.tagWord
  refine (FinalCall.hPrime_call_ok v name p.tagLen a (args.ready h) args.inputLength length).mono ?_
  intro t called
  refine ⟨?_, fun r hr => (called.regs r hr).trans (args.regs r hr), called.rd.trans args.keeps.rd,
    called.wr.trans args.keeps.wr, ?_⟩
  · have input : bytesAt a.mem (a.gpr .rdi) 1024 =
        serialize (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) := by
      rw [args.keeps.mem, args.input, ← Proof.Argon2.serialize_blockAt, block]
    rw [Proof.Argon2.finish_reduction]
    have digest := called.digest
    rw [args.output, input] at digest
    exact digest
  · have frame := called.frame
    rw [args.output, args.work, args.regs .rsp (by simp [calleeSaved]), args.keeps.mem] at frame
    exact frame

end VG.Proof.Argon2.X86_64.FinalOutput
end

/-! The complete reviewed finish computation, with its enclosing frame and ABI obligations. -/

namespace VG.Proof.Argon2.X86_64.Finish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

def writes (s : State) (p : Params) : List Region :=
  [⟨matrix s, 1024⟩, ⟨FinalOutput.output s, p.tagLen⟩,
    ⟨FinalOutput.work s, 16384⟩, below (s.gpr .rsp) 24]

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = Spec.Argon2.finish p memory
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa (Impl.Argon2.X86_64.Finish.code name (HPrime.hash v)) s (Done s · p memory) := by
  unfold Impl.Argon2.X86_64.Finish.code
  refine WP.seq ((FinalReduction.code_ok s p h.reduction memory represented).mono ?_)
  intro a reduced
  refine (FinalOutput.code_ok v name a p (output_ready h reduced) memory reduced.represented.accumulator).mono ?_
  intro t written
  have output : FinalOutput.output a = FinalOutput.output s := frame_word h.reduction reduced 256 (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := frame_word h.reduction reduced 248 (by decide)
  refine ⟨?_, fun r hr bx => (written.regs r hr).trans (reduced.regs r hr bx),
    written.rd.trans reduced.rd, written.wr.trans reduced.wr, ?_⟩
  · have digest := written.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := reduced.frame.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨_, by simp [writes], fun _ h => h⟩)
    have lastFrame := written.frame
    rw [output, work, reduced.regs .rsp (by simp [calleeSaved]) (by decide)] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.X86_64.Finish
end

/-! Merged from `Proof.Argon2.X86_64.FillFinishReady`. -/
section
/-! The complete filling loop retains the original final-call allocations and public metadata. -/

namespace VG.Proof.Argon2.X86_64.FillFinish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

theorem finish_ready {s t : State} {p : Params} {state : FillState}
    (filling : FillIterations.Ready p 0 s) (ready : Finish.Ready p s)
    (done : FillIterations.Finished s t p state) : Finish.Ready p t := by
  have bp := done.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)
  have sp := done.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)
  have base : matrix t = matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word filling 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word filling 248 (by decide) (by decide)
  constructor
  · have a := ready.reduction.allocation
    refine ⟨⟨a.positive, a.minimum, a.bound, ?_, ?_, ?_, ?_⟩, ready.reduction.lanesBound, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact a.read
    · rw [base, done.wr]; exact a.write
    · rw [base, bp]; exact a.frame
    · exact (done.regs .r12 (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans a.length
    · rw [done.rd, done.wr, bp]; exact ready.reduction.lanesRead
    · exact (done.frame_word filling 184 (by decide) (by decide)).trans ready.reduction.lanesWord
  · refine ⟨ready.output.positive, ready.output.bound, ?_,
      (done.frame_word filling 264 (by decide) (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact ready.output.reads
    · rw [base, done.rd, done.wr]; exact ready.output.input
    · rw [output, done.wr]; exact ready.output.outputWrite
    · rw [work, done.wr]; exact ready.output.workWrite
    · rw [base, work]; exact ready.output.inputWork
    · rw [output, work]; exact ready.output.outputWork
    · rw [sp, base]; exact ready.output.stackInput
    · rw [sp, output]; exact ready.output.stackOutput
    · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.X86_64.FillFinish
end

/-! The complete filling and finalization stages produce the reviewed final tag. -/

namespace VG.Proof.Argon2.X86_64.FillFinish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  filling : FillIterations.Ready p 0 s
  finish : Finish.Ready p s
  positive : 0 < p.passes

def writes (s : State) (p : Params) : List Region := FillIterations.writes s p ++ Finish.writes s p

structure Done (s t : State) (p : Params) (state : FillState) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen =
    Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes state).memory
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory) :
    WP isa (Impl.Argon2.X86_64.FillFinish.code name (HPrime.hash v)) s (Done s · p state) := by
  unfold Impl.Argon2.X86_64.FillFinish.code
  refine WP.seq ((FillIterations.loop_ok p.passes s p 0 h.filling state represented h.positive (Nat.zero_add _)).mono ?_)
  intro a filled
  refine (Finish.code_ok v name a p (finish_ready h.filling h.finish filled) _ filled.represented).mono ?_
  intro t finished
  have output : FinalOutput.output a = FinalOutput.output s := filled.frame_word h.filling 256 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := filled.frame_word h.filling 248 (by decide) (by decide)
  have base : matrix a = matrix s := filled.matrix
  refine ⟨?_, fun r hr bx sl ix => (finished.regs r hr bx).trans (filled.regs r hr bx sl ix),
    finished.rd.trans filled.rd, finished.wr.trans filled.wr, ?_⟩
  · have digest := finished.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := filled.frame.sub (by
      intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
    have lastFrame := finished.frame
    rw [Finish.writes, base, output, work,
      filled.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

end VG.Proof.Argon2.X86_64.FillFinish
