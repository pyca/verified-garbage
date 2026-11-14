module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.SievedBounds
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Function
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Public
import VerifiedGarbage.Proof.Framework.Arm.Exec
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Nat
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Incoming
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Sat
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Body
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Widen
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start

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
