module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Input
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Complete native ARMv7 safe-prime parameter generation satisfies the existing public correctness contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem correct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) (s : State)
    (pre : (Spec.Ffdh.parameterSearchContract abi 232).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.ParameterSearch.code (.call backend.candidateName backend.candidate)) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.parameterSearchContract abi 232).post s t := by
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
  have same : p.tail 0 p.attempts = Spec.Ffdh.parameterSearch p.c.bits p.c.generator p.attempts p.c.bytes := by
    rw [SearchParams.tail, List.drop_zero, VG.Proof.Ffdh.Generation.consume_zero]
  have statusFits : (p.tail 0 p.attempts).status < 2 ^ 32 := by
    cases p.tail 0 p.attempts <;> simp only [Spec.Ffdh.ParameterSearchResult.status] <;> decide
  have bytes := args.bytes
  simp only [State.addr] at bytes attemptsNat
  refine ⟨tr, t, run, abiOk, ?_⟩
  sig_post [Spec.Ffdh.parameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [args.out, args.used, args.tape, args.control, widthNat, bitsNat, genNat, tapeNat, bytes, attemptsNat]
  rw [← same]
  refine ⟨?_, result.output, result.used, result.policy⟩
  rw [result.status, BitVec.toNat_ofNat, Nat.mod_eq_of_lt statusFits]

end VG.Proof.Ffdh.Arm.ParameterSearch
