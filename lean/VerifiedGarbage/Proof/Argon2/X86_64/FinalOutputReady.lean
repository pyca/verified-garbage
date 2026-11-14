module

public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Contract
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitCall
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
import VerifiedGarbage.Proof.MdStream.X86_64.Common
public import VerifiedGarbage.Impl.Argon2.X86_64.FinalOutput
public import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLane
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Argon2.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub

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
