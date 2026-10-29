module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Ffdh.SievedContract

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Input
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Sat
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Framework.Arm.Exec
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Function
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Body
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Loop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Widen
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start
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
  refine ⟨?_, result.output, result.used, result.policy⟩
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
