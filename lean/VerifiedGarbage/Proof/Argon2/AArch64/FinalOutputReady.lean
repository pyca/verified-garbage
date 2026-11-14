module

public import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
public import VerifiedGarbage.Impl.Argon2.AArch64.FinalOutput
public import VerifiedGarbage.Proof.Argon2.AArch64.ReduceLane
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount

/-! ### `Argon2.AArch64.FinalCall`, which only this module used -/

section

/-! The final H′ call accepts a complete reduced block and a public tag length. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FinalCall

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)
open VG.Spec.Blake2 (bytesAt)

structure CallReady (len : Nat) (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  positive : 1 ≤ len
  bound : len < 2 ^ 32
  input : Covers [⟨s.gpr .x0, 1024⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .x2, len⟩] s.wr
  work : (⟨s.gpr .x4, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨s.gpr .x4, 16384⟩
  outputWork : (⟨s.gpr .x2, len⟩ : Region).Disjoint ⟨s.gpr .x4, 16384⟩
  stackInput : (below s.sp 16).Disjoint ⟨s.gpr .x0, 1024⟩
  stackOutput : (below s.sp 16).Disjoint ⟨s.gpr .x2, len⟩
  stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x4, 16384⟩

structure Called (len : Nat) (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .x2) len = Spec.Argon2.hPrime len (bytesAt s.mem (s.gpr .x0) 1024)
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x2, len⟩, ⟨s.gpr .x4, 16384⟩, below s.sp 16] s.mem t.mem

theorem hPrime_call_hyps (len : Nat) (s : State) (h : CallReady len s)
    (inputLength : s.gpr .x1 = 1024) (outputLength : s.gpr .x3 = BitVec.ofNat 64 len) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .x0, 1024⟩]
      [⟨s.gpr .x2, len⟩, ⟨s.gpr .x4, 16384⟩]) ∧
    Covers [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x2, len⟩, ⟨s.gpr .x4, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .x2, len⟩, ⟨s.gpr .x4, 16384⟩] s.wr := by
  have length : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bound (by decide))]
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp,
      g _ (by decide : Reg.x0 ∉ linkRegs), g _ (by decide : Reg.x1 ∉ linkRegs),
      g _ (by decide : Reg.x2 ∉ linkRegs), g _ (by decide : Reg.x3 ∉ linkRegs),
      g _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp,
      inputLength, outputLength, length]
    exact ⟨rfl, trivial, by decide, h.positive, h.bound, h.stackMinimum,
      h.inputWork, h.outputWork, h.stackInput, h.stackOutput, h.stackWork⟩
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

theorem hPrime_depth (v : HPrime.Backend) : (code v.hash).aarch64Depth = 1 := by
  simp only [code, Impl.Argon2.AArch64.HPrime.first,
    Impl.Argon2.AArch64.HPrime.chooseLength, Impl.Argon2.AArch64.HPrime.init,
    Impl.Argon2.AArch64.HPrime.absorbFixed, Impl.Argon2.AArch64.HPrime.update,
    Impl.Argon2.AArch64.HPrime.absorbInput, Impl.Argon2.AArch64.HPrime.finishInput,
    Impl.Argon2.AArch64.HPrime.finalize, Impl.Argon2.AArch64.HPrime.finishOutput,
    Impl.Argon2.AArch64.HPrime.extendDigest, Impl.Argon2.AArch64.HPrime.emitPrefix,
    Impl.Argon2.AArch64.HPrime.copy, Impl.Argon2.AArch64.HPrime.chain,
    Impl.Argon2.AArch64.HPrime.next, Impl.Argon2.AArch64.HPrime.copyRemaining,
    Code.aarch64Depth, v.ok.initDepth, v.ok.updateDepth, v.ok.finalizeDepth]
  rfl

theorem hPrime_call_ok (v : HPrime.Backend) (name : String)
    (len : Nat) (s : State) (h : CallReady len s) (inputLength : s.gpr .x1 = 1024)
    (outputLength : s.gpr .x3 = BitVec.ofNat 64 len) :
    WP isa (.call name (code v.hash)) s (Called len s) := by
  obtain ⟨pre, cover, writes⟩ := hPrime_call_hyps len s h inputLength outputLength
  refine WP.callF (k := HPrime.localContract) (HPrime.code_correct v) pre cover writes ?_
    (by rw [hPrime_depth]; decide)
  intro t rd wr sp frame regs digest
  change bytesAt t.mem (s.callEntry.gpr .x2) (s.callEntry.gpr .x3).toNat =
    Spec.Argon2.hPrime (s.callEntry.gpr .x3).toNat
      (bytesAt s.mem (s.callEntry.gpr .x0) (s.callEntry.gpr .x1).toNat) at digest
  rw [State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), inputLength, outputLength,
    show (1024 : Addr).toNat = 1024 from rfl,
    show (BitVec.ofNat 64 len).toNat = len from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bound (by decide))]] at digest
  refine ⟨digest, ?_, sp, rd, wr, ?_⟩
  · intro r hr
    have preserved : r ∈ VG.AArch64.preserved ∧ r ≠ .x30 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact regs r preserved.1 preserved.2
  · simpa only [hPrime_depth, Nat.mul_one, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.FinalCall

end

end


/-! Merged from `Proof.Argon2.AArch64.FinalOutputArgs`. -/

@[expose] public section

section
/-! Load the public final-call pointers and tag length from the enclosing frame. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

def output (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 256) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

def changed : List Reg := [.x0, .x1, .x2, .x3, .x4]

structure Arguments (s t : State) : Prop where
  input : t.gpr .x0 = ReductionState.matrix s
  inputLength : t.gpr .x1 = 1024
  output : t.gpr .x2 = output s
  outputLength : t.gpr .x3 = s.mem.readW (off (s.gpr .x19) 264) 64
  work : t.gpr .x4 = work s
  keeps : Divide.Keeps changed s t

theorem args_ok (s : State) (read : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    WP isa (.block Impl.Argon2.AArch64.FinalOutput.args) s (Arguments s) := by
  have input := read 232 (by simp)
  have out := read 256 (by simp)
  have len := read 264 (by simp)
  have scratch := read 248 (by simp)
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.FinalOutput.args,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.imm,
    show 1024 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide,
    show 256 % 8 = 0 ∧ 256 < 4096 * 8 from by decide,
    show 264 % 8 = 0 ∧ 264 < 4096 * 8 from by decide,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1024#16).setWidth 64 = 1024#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    input, out, len, scratch, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · constructor
    · intro r hr
      simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    all_goals rfl

theorem Arguments.regs {s t : State} (h : Arguments s t) (r : Reg) (hr : r ∈ FillCompress.loopRegs) : t.gpr r = s.gpr r := by
  have unchanged : r ∉ changed := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.keeps.regs r unchanged

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! Final output uses matrix block zero and the original disjoint hash scratch allocation. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  positive : 1 ≤ p.tagLen
  bound : p.tagLen < 2 ^ 32
  reads : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  tagWord : s.mem.readW (off (s.gpr .x19) 264) 64 = BitVec.ofNat 64 p.tagLen
  input : Covers [⟨ReductionState.matrix s, 1024⟩] (s.rd ++ s.wr)
  outputWrite : Covers [⟨output s, p.tagLen⟩] s.wr
  workWrite : (⟨work s, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨ReductionState.matrix s, 1024⟩ : Region).Disjoint ⟨work s, 16384⟩
  outputWork : (⟨output s, p.tagLen⟩ : Region).Disjoint ⟨work s, 16384⟩
  stackInput : (below s.sp 16).Disjoint ⟨ReductionState.matrix s, 1024⟩
  stackOutput : (below s.sp 16).Disjoint ⟨output s, p.tagLen⟩
  stackWork : (below s.sp 16).Disjoint ⟨work s, 16384⟩

theorem Arguments.ready {p : Params} {s t : State} (h : Ready p s) (a : Arguments s t) :
    FinalCall.CallReady p.tagLen t := by
  have sp := a.keeps.sp
  constructor
  · rw [sp]; exact h.stackMinimum
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

end VG.Proof.Argon2.AArch64.FinalOutput
