module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.SievedBounds
import VerifiedGarbage.Proof.Framework.Arm.Exec
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Nat
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Sat
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTFinish
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Finish
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Step
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LoopGuard
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CompareResult
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePre

/-! ### `Ffdh.Arm.ParameterSearch.Public`, which only this module used -/

section

/-! Read all search parameters and persistent policy from the existing public ARMv7 signature. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

structure SearchAbi (p : SearchParams) (s : State) : Prop extends
    VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateAbi p.c s where
  control : stackArg s 5 = p.control
  counter : s.mem.readW (State.addr p.control) 64 = BitVec.ofNat 64 p.attempts
  widthPolicy : s.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.c.length
  entropyPolicy : s.mem.readW (off (State.addr p.control) 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)

theorem searchPublic (s : State) (pre : (Spec.Ffdh.sievedParameterSearchContract abi 232).pre s) :
    ∃ p, SearchAbi p s := by
  sig_pre [Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, outUsed, outTape, outScratch, outControl, _, usedTape, usedScratch, usedControl, _,
    tapeScratch, tapeControl, scratchControl, _, _, _, _, _, _, _, _,
    outFit, usedFit, tapeFit, scratchFit, controlFit, lower, upper, width, generator, space,
    attemptsBound, widthPolicy, entropyPolicy, tapeBound⟩ := pre
  let rb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  have rbLength : rb.length = (stackArg s 2).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let q : VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams := {
    out := s.gpr .r0, usedPtr := s.gpr .r2, tape := stackArg s 1, base := stackArg s 3
    bits := (s.gpr .r3).toNat, generator := (stackArg s 0).toNat, capacity := (stackArg s 4).toNat, bytes := rb
    minBits := lower, maxBits := upper, generatorAllowed := generator
    space := by rw [← width]; exact space
    scratchFits := by simpa only [Nat.mul_comm 8] using scratchFit
    outputFits := by rw [← width]; exact outFit
    usedFits := usedFit
    tapeFits := by rw [rbLength]; exact tapeFit
    tapeCount := by rw [rbLength]; exact (stackArg s 2).isLt
    outputUsed := by rw [← width]; exact outUsed
    outputScratch := by rw [← width]; simpa only [Nat.mul_comm 8, State.addr] using outScratch
    outputTape := by rw [← width, rbLength]; exact outTape
    usedScratch := by simpa only [Nat.mul_comm 8, State.addr] using usedScratch
    usedTape := by rw [rbLength]; exact usedTape
    tapeScratch := by rw [rbLength]; simpa only [Nat.mul_comm 8, State.addr] using tapeScratch }
  let p : SearchParams := {
    candidate := q, control := stackArg s 5,
    attempts := (s.mem.readW (State.addr (stackArg s 5)) 64).toNat
    attemptsBound := attemptsBound
    tapeBound := by rw [rbLength]; exact tapeBound
    controlFits := controlFit
    controlOutput := by
      change (⟨State.addr (stackArg s 5), 128⟩ : Region).Disjoint
        ⟨State.addr (s.gpr .r0), ((s.gpr .r3).toNat + 7) / 8⟩
      rw [← width]
      exact outControl.symm
    controlUsed := usedControl.symm
    controlScratch := by simpa only [Nat.mul_comm 8, State.addr] using scratchControl.symm
    controlTape := by rw [rbLength]; exact tapeControl.symm }
  refine ⟨p, ⟨?_, rfl, ?_, ?_, ?_⟩⟩
  · refine ⟨rfl, ?_, rfl, ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
    · change s.gpr .r1 = BitVec.ofNat 32 (((s.gpr .r3).toNat + 7) / 8)
      rw [← width, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [p, q, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [p, q, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change stackArg s 2 = BitVec.ofNat 32 rb.length
      rw [rbLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [p, q, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) rb.length = rb
      rw [rbLength]
  · simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change s.mem.readW (off (State.addr (stackArg s 5)) 8) 64 =
      BitVec.ofNat 64 (((s.gpr .r3).toNat + 7) / 8)
    rw [← width]
    exact widthPolicy
  · exact entropyPolicy

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.Function`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterSearch.Widen`, which this module and modules that import it used -/

section

/-! The search runs without permission to overwrite its saved registers; widening restores caller permissions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem SearchBuffers.withRegions {p : SearchParams} {s : State} {rd wr : List Region}
    (h : SearchBuffers p s) (reads : Covers (s.rd ++ s.wr) (rd ++ wr))
    (writes : ∀ r ∈ s.wr, r ∈ wr) : SearchBuffers p (s.withRegions rd wr) :=
  ⟨⟨⟨h.controller.space.1, writes _ h.controller.space.2⟩, h.controller.ptr⟩,
    ⟨h.output.1, writes _ h.output.2⟩, ⟨h.used.1, writes _ h.used.2⟩,
    ⟨h.scratch.1, writes _ h.scratch.2⟩, reads _ _ h.tapeRead, h.tapeBytes,
    reads _ _ h.stack, h.below, h.stackSeparate⟩

theorem SearchDone.withRegions {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} {rd wr : List Region} (h : SearchDone p result s)
    (reads : Covers (s.rd ++ s.wr) (rd ++ wr)) (writes : ∀ r ∈ s.wr, r ∈ wr) :
    SearchDone p result (s.withRegions rd wr) :=
  ⟨h.buffers.withRegions reads writes, h.usedBound, h.usedPtr, h.used, h.status, h.policy, h.output⟩

theorem SearchStart.withRegions {p : SearchParams} {s : State} {rd wr : List Region}
    (h : SearchStart p s) (reads : Covers (s.rd ++ s.wr) (rd ++ wr))
    (writes : ∀ r ∈ s.wr, r ∈ wr) : SearchStart p (s.withRegions rd wr) := by
  refine ⟨h.storage.withRegions reads writes, ⟨?_, h.incoming.separate⟩,
    h.out, h.used, h.bits, h.counter, h.width, h.entropy⟩
  intro i hi
  have old := h.incoming.incoming i hi
  exact ⟨old.fits, reads _ _ old.readable, old.word⟩

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.Body`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterSearch.Loop`, which only this module used -/

section

/-! Total correctness of the native safe-prime search loop, with its full u64 attempt measure. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

def SearchInvariant (p : SearchParams) (start : State) (expected : Spec.Ffdh.ParameterSearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used remaining, n = remaining + 1 ∧ SearchLive p used remaining s ∧
    expected = p.tail used remaining ∧ Rest searchClobbers start s

def SearchFinished (p : SearchParams) (start : State) (expected : Spec.Ffdh.ParameterSearchResult)
    (s : State) : Prop := SearchDone p expected s ∧ Rest searchClobbers start s

theorem iteration (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {start s : State} {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (inv : SearchInvariant p start expected n s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) s fun t =>
      (isa.eval .eq t = some false ∧ SearchFinished p start expected t) ∨
      (isa.eval .eq t = some true ∧ ∃ m < n, SearchInvariant p start expected m t) := by
  obtain ⟨used, remaining, measure, h, same, initialRest⟩ := inv
  have done : ∀ t, SearchDone p expected t → Rest searchClobbers start t →
      WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 13, .cmp .r9 (.imm 4)]) t fun t =>
        (isa.eval .eq t = some false ∧ SearchFinished p start expected t) ∨
        (isa.eval .eq t = some true ∧ ∃ m < n, SearchInvariant p start expected m t) := by
    intro t finished rest
    refine WP.mono finished.loop_guard ?_
    rintro u ⟨⟨flag, result⟩, restU⟩
    exact Or.inl ⟨flag, result, rest.trans (restU.mono (by simp [searchClobbers]))⟩
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.iteration
  refine WP.seq (WP.mono h.budget_guard fun u ⟨⟨liveU, flag, _⟩, restU⟩ => ?_)
  have restSU : Rest searchClobbers start u := initialRest.trans (restU.mono (by simp [searchClobbers]))
  apply WP.seq
  refine WP.ite _ (by change some u.z = _; rw [flag]) ?_ ?_
  · intro zero
    have zero' := of_decide_eq_true zero
    refine WP.mono liveU.exhausted ?_
    rintro t ⟨finished, restT⟩
    have result : expected = .exhausted used := by rw [same, zero']; rfl
    rw [← result] at finished
    exact done t finished (restSU.trans restT)
  · intro nonzero
    have positive : 0 < remaining := Nat.pos_of_ne_zero (of_decide_eq_false nonzero)
    refine WP.mono (liveU.step backend positive) ?_
    rintro t ⟨classified, restT⟩
    have restST := restSU.trans restT
    cases result : candidateResult p used with
    | none =>
      simp only [Classified, result] at classified
      rw [← same] at classified
      exact done t classified restST
    | some pair =>
      obtain ⟨prime, rand⟩ := pair
      cases prime with
      | some prime =>
        simp only [Classified, result] at classified
        rw [← same] at classified
        exact done t classified restST
      | none =>
        simp only [Classified, result] at classified
        refine WP.mono (classified.1.loop_guard classified.2) ?_
        rintro q ⟨⟨flagQ, liveQ⟩, restQ⟩
        refine Or.inr ⟨flagQ, remaining, by omega_using [measure], used + candidateUsed p used, remaining - 1,
          by omega_using [positive], liveQ, same.trans (p.tail_reject positive result),
          restST.trans (restQ.mono (by simp [searchClobbers]))⟩

theorem loop (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {start s : State} {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (inv : SearchInvariant p start expected n s) :
    WP isa (.loop (VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) .eq)
      s (SearchFinished p start expected) :=
  WP.loop (M := isa)
    (body := VG.Impl.Ffdh.Arm.ParameterSearch.iteration (.call backend.candidateName backend.candidate)) (c := .eq)
    (Q := SearchFinished p start expected) (SearchInvariant p start expected)
    (fun _ _ h => iteration backend h) n s inv

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! The complete native search body preserves its caller's registers and writes only its buffers and outgoing stack. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Stack.lean`, which only this module imported.
section

/-! The full parameter search uses 24 saved bytes and 24 outgoing bytes above the 184-byte candidate. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem iteration_stack (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterSearch.iteration
      (.call backend.candidateName backend.candidate)) ≤ 208 := by
  have bound := backend.candidateStack
  simp only [VG.Impl.Ffdh.Arm.ParameterSearch.iteration,
    VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep, VG.Impl.Ffdh.Arm.ParameterSearch.candidateRun,
    VG.Impl.Ffdh.Arm.ParameterSearch.classify, VG.Impl.Ffdh.Arm.ParameterSearch.short,
    VG.Impl.Ffdh.Arm.ParameterSearch.exhausted, VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut,
    VG.Impl.Ffdh.Arm.ParameterSearch.request, VG.Impl.Ffdh.Arm.ParameterSearch.select,
    VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros,
    FrameStack.armStack, Bool.false_eq_true, ite_true, ite_false, Nat.zero_max, Nat.max_zero]
  omega

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

def bodyClobbers : List Reg := [.r0, .r1, .r2, .r3, .r4, .r9, .r10, .r11, .r12, .lr]

theorem body_ok (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {s : State} (h : SearchStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate)) s fun t =>
      SearchDone p (p.tail 0 p.attempts) t ∧ Rest bodyClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.body
  refine WP.seq (WP.mono h.entry fun u ⟨live, rest⟩ => ?_)
  have inv : SearchInvariant p u (p.tail 0 p.attempts) (p.attempts + 1) u :=
    ⟨0, p.attempts, rfl, live, rfl, Rest.refl _ _⟩
  refine WP.mono (loop backend inv) ?_
  rintro t ⟨finished, restT⟩
  exact ⟨finished, (rest.mono (by simp [bodyClobbers])).trans (restT.mono (by simp [bodyClobbers, searchClobbers]))⟩

theorem body_run (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {s : State} (h : SearchStart p s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate)) s tr t ∧
      SearchDone p (p.tail 0 p.attempts) t ∧ Rest bodyClobbers s t ∧
      Frame (s.wr ++ [FrameStack.belowA s.sp 208]) s.mem t.mem := by
  obtain ⟨tr, t, run, done, rest⟩ := body_ok backend h
  have bound : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterSearch.body
      (.call backend.candidateName backend.candidate)) ≤ 208 := by
    simpa only [VG.Impl.Ffdh.Arm.ParameterSearch.body, FrameStack.armStack, Nat.zero_max] using iteration_stack backend
  have fit : 208 ≤ s.sp.toNat := h.storage.below
  exact ⟨tr, t, run, done, rest, FrameStack.Frame.belowA_mono (FrameStack.Exec.frameSp run (Nat.le_trans bound fit)) bound fit⟩

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.Push`, which this module and modules that import it used -/

section

/-! The parameter search reuses the established ARMv7 24-byte saved-register frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

abbrev searchPushed (s : State) : State := pushed [.r4, .r9, .r10, .r11, .r12, .lr] s

def bodyState (s : State) : State := (searchPushed s).withRegions
  (⟨State.addr (searchPushed s).sp, 24⟩ :: s.rd) s.wr

theorem push_saved (s : State) (fit : 24 ≤ s.sp.toNat) :
    Spill.Saved (bodyState s).mem (State.addr (bodyState s).sp) s.gpr savedSlots := by
  exact VG.Proof.Ffdh.Arm.KeySearch.push_saved s fit

theorem body_writes (s : State) : Covers (bodyState s).wr (searchPushed s).wr :=
  Covers.of_mem fun _ member => List.mem_cons_of_mem _ member

theorem body_reads (s : State) :
    Covers ((bodyState s).rd ++ (bodyState s).wr) ((searchPushed s).rd ++ (searchPushed s).wr) := by
  apply Covers.of_mem
  intro r member
  change r ∈ (⟨State.addr (searchPushed s).sp, 24⟩ :: s.rd) ++ s.wr at member
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with (rfl | read) | write
  · exact List.mem_append_right _ (List.mem_cons_self)
  · exact List.mem_append_left _ read
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ write)

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! Execute the full native function while keeping its saved frame read-only during search. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

structure FunctionInput (p : SearchParams) (s : State) : Prop where
  stackFits : 232 ≤ s.sp.toNat
  start : SearchStart p (bodyState s)
  savedWrites : ∀ r ∈ s.wr, (⟨State.addr (bodyState s).sp, 24⟩ : Region).Disjoint r

theorem function_body (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {s : State} (h : FunctionInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate))
      (searchPushed s) (FinishInput p s (p.tail 0 p.attempts)) := by
  obtain ⟨tr, t, run, done, rest, frame⟩ := body_run backend h.start
  have fit : 24 ≤ s.sp.toNat := by have := h.stackFits; omega_using [this]
  have saved : Spill.Saved t.mem (State.addr t.sp) s.gpr savedSlots := by
    rw [rest.sp]
    apply (push_saved s fit).frame (lo := 0) (hi := 24) (by decide) frame
    intro r member
    have separate : (⟨State.addr (bodyState s).sp, 24⟩ : Region).Disjoint r := by
      rcases List.mem_append.mp member with original | below
      · exact h.savedWrites r original
      · obtain rfl := List.mem_singleton.mp below
        have below : 208 ≤ (bodyState s).sp.toNat := h.start.storage.below
        rw [FrameStack.belowA, FrameStack.addr_sub' below]
        exact VG.Offset.base_disjoint_below _ (by decide : 208 + 24 ≤ 2 ^ 64)
    simpa only [BitVec.add_zero, Nat.sub_zero] using separate
  have widened := Exec.widen run (body_reads s) (body_writes s)
  have runWide : Exec isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate))
      (searchPushed s) tr (t.withRegions (searchPushed s).rd (searchPushed s).wr) := by
    simpa only [bodyState, State.withRegions_withRegions, State.withRegions_self] using widened
  refine ⟨tr, _, runWide, ?_⟩
  refine ⟨done.withRegions ?_ ?_, saved, rest.sp, fit, ?_⟩
  · rw [rest.rd, rest.wr]
    exact body_reads s
  · intro r member
    rw [rest.wr] at member
    exact List.mem_cons_of_mem _ member
  · intro r member
    exact rest.gpr r (by cases r <;> simp_all [bodyClobbers])

theorem function_ok (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {s : State} (h : FunctionInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate)) s
      fun t => abiPreserved s t ∧ ResultPost p (p.tail 0 p.attempts) t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.code
  refine WP.frame (by decide) (by change 24 ≤ s.sp.toNat; have := h.stackFits; omega_using [this]) (by decide) ?_
  rw [WP.seq_iff]
  exact WP.mono (function_body backend h) fun _ input => finish_ok input

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.Input`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterSearch.Layout`, which only this module used -/

section

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
    (pre : (Spec.Ffdh.sievedParameterSearchContract abi 232).pre s) (args : SearchAbi p s) : SearchLayout p s := by
  sig_pre [Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, _, _, _, _, _, _, _, _, _, _, controlArgs,
    stackOut, stackUsed, stackTape, stackScratch, stackControl, stackArgs, _⟩ := pre
  have widthNat : (s.gpr .r1).toNat = p.c.length := by
    rw [args.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.width_bounds; omega_using [this])]
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

end

end

/-! The unchanged public signature provides all inputs for the verified native search function. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/PushedArguments.lean`, which only this module imported.
section

/-! All six public ARM stack arguments survive the saved-register push and remain readable. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

theorem SearchAbi.incoming_value {p : SearchParams} {s : State} (args : SearchAbi p s)
    {i : Nat} (bound : i < 6) : stackArg s i = incomingValue p i := by
  have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  · exact args.generator
  · exact args.tape
  · exact args.tapeLength
  · exact args.base
  · exact args.capacity
  · exact args.control

theorem pushed_arguments {p : SearchParams} {s : State}
    (h : SearchLayout p s) (args : SearchAbi p s) : EntryArguments p (bodyState s) := by
  have fit := h.stackFits
  have argsFit := h.argsFits
  have native (i : Nat) (hi : i < 6) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega)
  have wholeRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 24 :=
    ⟨_, List.mem_append_left _ (by rw [h.reads]; simp [readRegions]), Region.contains_self _ _⟩
  have pushedFrame : Frame [FrameStack.belowA s.sp 24] s.mem (bodyState s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by omega : 24 ≤ s.sp.toNat)
  have savedSub : (FrameStack.belowA s.sp 24).Sub (FrameStack.belowA s.sp 232) :=
    FrameStack.belowA_sub (by decide) fit
  have argsSaved : (⟨State.addr s.sp, 24⟩ : Region).Disjoint (FrameStack.belowA s.sp 24) :=
    ((h.stackSeparate _ (by simp [readRegions])).sub_left savedSub).symm
  have offsetAddress (i : Nat) (hi : i < 6) :
      off (State.addr (bodyState s).sp) (24 + 4 * i) = stackArgAddr s i := by
    have room : (bodyState s).sp.toNat + (24 + 4 * i) < 2 ^ 32 := by
      change (s.sp - 24#32).toNat + (24 + 4 * i) < 2 ^ 32
      rw [FrameStack.sub_toNat' (by omega : 24 ≤ s.sp.toNat)]
      omega
    change State.addr (bodyState s).sp + BitVec.ofNat 64 (24 + 4 * i) = _
    rw [← VG.Arm.addr_add room]
    change State.addr (s.sp - 24#32 + BitVec.ofNat 32 (24 + 4 * i)) = _
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rfl
  refine ⟨?_, ?_⟩
  · intro i hi
    refine ⟨?_, ?_, ?_⟩
    · change (s.sp - 24#32).toNat + (24 + 4 * i) + 4 ≤ 2 ^ 32
      rw [FrameStack.sub_toNat' (by omega : 24 ≤ s.sp.toNat)]
      omega
    · rw [offsetAddress i hi, native i hi]
      obtain ⟨r, member, contains⟩ := CallLay.inRegions_sub wholeRead (by omega : 4 * i + 4 ≤ 24) (by decide)
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp member with read | write
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ read)
      · exact List.mem_append_right _ write
    · rw [offsetAddress i hi]
      have sub : (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨State.addr s.sp, 24⟩ := by
        rw [native i hi]
        exact Offset.sub_base _ (by omega)
      exact (pushedFrame.readW (w := 32) (a := stackArgAddr s i) (r := ⟨stackArgAddr s i, 4⟩)
        (Region.contains_self _ _) (by simpa using argsSaved.sub_left sub) (by decide)).trans (args.incoming_value hi)
  · intro i hi
    rw [offsetAddress i hi]
    apply h.controlArgs.symm.sub_left
    rw [native i hi]
    exact Offset.sub_base _ (by omega)

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/PushMemory.lean`, which only this module imported.
section

/-! The native saved-register push preserves the entropy tape and every public policy word. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

theorem SearchLayout.push_word {p : SearchParams} {s : State} (h : SearchLayout p s)
    {j : Nat} (bound : j < 16) :
    (bodyState s).mem.readW (off (State.addr p.control) (8 * j)) 64 =
      s.mem.readW (off (State.addr p.control) (8 * j)) 64 := by
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (bodyState s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; have := h.stackFits; omega)
  have separate := (h.stackSeparate ⟨State.addr p.control, 128⟩ (by simp [writeRegions])).sub_left
    (FrameStack.belowA_sub (by decide : 24 ≤ 232) h.stackFits)
  exact frame.readW (r := ⟨State.addr p.control, 128⟩)
    (Offset.contains_base _ (by omega : 8 * j + 8 ≤ 128) (by omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate.symm) (by decide)

theorem SearchLayout.push_bytes {p : SearchParams} {s : State} (h : SearchLayout p s)
    (args : SearchAbi p s) :
    Spec.Rsa.bytesAt (bodyState s).mem (State.addr p.c.tape) p.c.bytes.length = p.c.bytes := by
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (bodyState s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; have := h.stackFits; omega)
  have separate := (h.stackSeparate ⟨State.addr p.c.tape, p.c.bytes.length⟩
    (by simp [readRegions])).sub_left (FrameStack.belowA_sub (by decide : 24 ≤ 232) h.stackFits)
  exact (VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by have := p.c.tapeCount; omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate.symm)).trans args.bytes

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm

theorem searchInput {p : SearchParams} {s : State}
    (pre : (Spec.Ffdh.sievedParameterSearchContract abi 232).pre s) (args : SearchAbi p s) : FunctionInput p s := by
  have layout := searchLayout pre args
  have fit := layout.stackFits
  have savedSub : (⟨State.addr (bodyState s).sp, 24⟩ : Region).Sub (FrameStack.belowA s.sp 232) :=
    FrameStack.belowA_sub (by decide) fit
  have belowSub : (FrameStack.belowA (bodyState s).sp 208).Sub (FrameStack.belowA s.sp 232) :=
    FrameStack.belowA_inner (by decide) fit
  have storage : SearchBuffers p ((bodyState s).setReg .r4 p.control) := by
    refine ⟨⟨⟨p.controlFits, ?_⟩, ?_⟩, ⟨p.c.outputFits, ?_⟩, ⟨p.c.usedFits, ?_⟩,
      ⟨p.c.scratchFits, ?_⟩, ?_, layout.push_bytes args, ?_, ?_, ?_⟩
    · change (⟨State.addr p.control, 128⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · simp only [State.setReg, ite_true]
    · change (⟨State.addr p.c.out, p.c.length⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · change (⟨State.addr p.c.usedPtr, 8⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · change (⟨State.addr p.c.base, 8 * p.c.capacity⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · refine ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ ?_), Region.contains_self _ _⟩
      rw [layout.reads]; simp [readRegions]
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_self), Region.contains_self _ _⟩
    · change 208 ≤ (s.sp - 24#32).toNat
      rw [FrameStack.sub_toNat' (by omega_using [fit] : 24 ≤ s.sp.toNat)]
      omega_using [fit]
    · intro r member
      have original : r ∈ writeRegions p ++ readRegions p s.sp := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [writeRegions, readRegions]
      exact ⟨(layout.stackSeparate r original).sub_left savedSub,
        (layout.stackSeparate r original).sub_left belowSub⟩
  have initial : SearchStart p (bodyState s) := by
    refine ⟨storage, pushed_arguments layout args, args.out, args.used, args.bits, ?_, ?_, ?_⟩
    · have word := layout.push_word (j := 0) (by decide)
      have address : VG.Proof.Mont.off (State.addr p.control) 0 = State.addr p.control := by simp [VG.Proof.Mont.off]
      rw [show 8 * 0 = 0 from rfl, address] at word
      exact word.trans args.counter
    · exact (layout.push_word (j := 1) (by decide)).trans args.widthPolicy
    · exact (layout.push_word (j := 2) (by decide)).trans args.entropyPolicy
  refine ⟨fit, initial, ?_⟩
  intro r member
  rw [layout.writes] at member
  exact (layout.stackSeparate r (List.mem_append_left _ member)).sub_left savedSub

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! Complete correctness, public timing and satisfiability for native ARMv7 parameter generation. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Correct.lean`, which only this module imported.
section

/-! Complete native ARMv7 safe-prime parameter generation satisfies the existing public correctness contract. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem correct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) (s : State)
    (pre : (Spec.Ffdh.sievedParameterSearchContract abi 232).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate)) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.sievedParameterSearchContract abi 232).post s t := by
  obtain ⟨p, args⟩ := searchPublic s pre
  obtain ⟨tr, t, run, abiOk, result⟩ := function_ok backend (searchInput pre args)
  have widthNat : (s.gpr .r1).toNat = p.c.length := by
    rw [args.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.width_bounds; omega)]
  have bitsNat : (s.gpr .r3).toNat = p.c.bits := by
    rw [args.bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.maxBits; omega)]
  have genNat : (stackArg s 0).toNat = p.c.generator := by
    rw [args.generator, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases p.c.generatorAllowed with eq | eq <;> omega)]
  have tapeNat : (stackArg s 2).toNat = p.c.bytes.length := by
    rw [args.tapeLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.c.tapeCount]
  have attemptsNat : (s.mem.readW (State.addr p.control) 64).toNat = p.attempts := by
    rw [args.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.attempts_bound; omega)]
  have same : p.tail 0 p.attempts = Spec.Ffdh.sievedParameterSearch p.c.bits p.c.generator p.attempts p.c.bytes := by
    rw [SearchParams.tail, List.drop_zero, VG.Proof.Ffdh.Generation.consume_zero]
  have statusFits : (p.tail 0 p.attempts).status < 2 ^ 32 := by
    cases p.tail 0 p.attempts <;> simp only [Spec.Ffdh.ParameterSearchResult.status] <;> decide
  have bytes := args.bytes
  simp only [State.addr] at bytes attemptsNat
  refine ⟨tr, t, run, abiOk, ?_⟩
  sig_post [Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [args.out, args.used, args.tape, args.control, widthNat, bitsNat, genNat, tapeNat, bytes, attemptsNat]
  rw [← same]
  refine ⟨?_, result.output, result.used, _, result.policy,
    by rw [same]; exact SievedGeneration.search_requests _ _ _ _⟩
  rw [result.status, BitVec.toNat_ofNat, Nat.mod_eq_of_lt statusFits]

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/CTFunction.lean`, which only this module imported.
section

/-! Native entry, complete bounded search, return stores and saved frame satisfy relational timing. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

theorem body_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two SearchStart)
    (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.body
  refine RelCT.seq (two_post entry_ct entry_ready) ?_
  exact (loop_ct backend).mono
    (fun _ _ ⟨p, hs, ht, sp⟩ => ⟨initialPoint p, hs, ht, sp⟩) (fun _ _ h => h)

private theorem body_ready (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    (p : SearchParams) (s : State) (h : SearchStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate)) s (DoneCT p) :=
  WP.mono (body_ok backend h) fun _ ⟨done, _⟩ => ⟨_, done⟩

theorem function_body_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two SearchStart)
    (.seq (VG.Impl.Ffdh.Arm.ParameterSearch.body (.call backend.candidateName backend.candidate))
      (.block VG.Impl.Ffdh.Arm.ParameterSearch.finish)) (fun _ _ => True) :=
  RelCT.seq (two_post (body_ct backend) (body_ready backend)) finish_ct

private theorem pushed_start {p : SearchParams} {s : State} (h : FunctionInput p s) : SearchStart p (searchPushed s) := by
  have result := h.start.withRegions (body_reads s) (fun _ member => List.mem_cons_of_mem _ member)
  simpa only [bodyState, State.withRegions_withRegions, State.withRegions_self] using result

private theorem push_search_eq {s t : State}
    (h : isa.push (.push [.r4, .r9, .r10, .r11, .r12, .lr]) s = some t) : t = searchPushed s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem function_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two FunctionInput)
    (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.code
  refine RelCT.frame (fun _ _ ⟨_, _, _, sp⟩ => sp) ?_
  refine (function_body_ct backend).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s, t, ⟨p, hs, ht, sp⟩, pushS, pushT⟩
  have first := push_search_eq pushS
  have second := push_search_eq pushT
  subst first second
  refine ⟨p, pushed_start hs, pushed_start ht, ?_⟩
  change s.sp - 24#32 = t.sp - 24#32
  rw [sp]

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem constantTime (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    ConstantTime isa (Spec.Ffdh.sievedParameterSearchContract abi 232).pre (Spec.Ffdh.sievedParameterSearchContract abi 232).pub
      (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate)) := by
  intro s t traceS traceT u v hs ht pub runS runT
  obtain ⟨p, args⟩ := searchPublic s hs
  sig_pub [Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pub
  obtain ⟨sp, leak, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := pub
  obtain ⟨bytes, policy⟩ := List.append_inj leak (by
    simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, p6])
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have policyEq := congrArg (List.map (BitVec.ofNat 64)) policy
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at policyEq
  rw [← p9, args.control] at policyEq
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero] at policyEq
  obtain ⟨word0, tail1⟩ := List.cons.inj policyEq
  obtain ⟨word1, tail2⟩ := List.cons.inj tail1
  obtain ⟨word2, _⟩ := List.cons.inj tail2
  have argsT : SearchAbi p t := {
    out := p0.symm.trans args.out
    width := p1.symm.trans args.width
    used := p2.symm.trans args.used
    bits := p3.symm.trans args.bits
    generator := p4.symm.trans args.generator
    tape := p5.symm.trans args.tape
    tapeLength := p6.symm.trans args.tapeLength
    base := p7.symm.trans args.base
    capacity := p8.symm.trans args.capacity
    bytes := by
      rw [← p5, ← p6, args.tape, args.tapeLength] at byteEq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.c.tapeCount] at byteEq
      exact byteEq.symm.trans args.bytes
    control := p9.symm.trans args.control
    counter := word0.symm.trans args.counter
    widthPolicy := word1.symm.trans args.widthPolicy
    entropyPolicy := word2.symm.trans args.entropyPolicy }
  exact ((function_ct backend) _ _ _ _ _ _
    ⟨p, searchInput hs args, searchInput ht argsT, sp⟩ runS runT).1

theorem verified (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    Verified target (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate))
      (Spec.Ffdh.sievedParameterSearchContract abi 232) :=
  ⟨correct backend, constantTime backend, search_sat⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
