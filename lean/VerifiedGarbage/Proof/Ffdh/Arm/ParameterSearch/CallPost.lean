module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentWords
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallFacts
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! Interpret the native candidate result using exactly the remaining public tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

def candidateResult (p : SearchParams) (used : Nat) :=
  Spec.Ffdh.sievedParameterCandidate p.c.bits p.c.generator (p.c.bytes.drop used)

def candidateUsed (p : SearchParams) (used : Nat) : Nat :=
  match candidateResult p used with
  | some (_, rest) => p.c.bytes.length - used - rest.length
  | none => 0

structure CandidatePost (p : SearchParams) (used : Nat) (s : State) : Prop where
  status : (s.gpr .r0).toNat = Proof.Ffdh.candidateStatus (candidateResult p used)
  output : Spec.Rsa.bytesAt s.mem (State.addr p.c.out) p.c.length =
    match candidateResult p used with
    | some (some prime, _) => Spec.Rsa.i2osp prime p.c.length
    | _ => List.replicate p.c.length 0
  consumed : Spec.Rsa.wordsAt s.mem (State.addr (p.control + 112#32)) 1 =
    [BitVec.ofNat 64 (candidateUsed p used)]

theorem call_post {p : SearchParams} {used : Nat} {s t : State} {m : Mem}
    (facts : CallFacts p used s.sp) (args : ArgumentContext p used s)
    (memory : s.mem = callMem p used m s.sp)
    (bytes : Spec.Rsa.bytesAt s.mem (State.addr (p.c.tape + BitVec.ofNat 32 used))
      (p.c.bytes.length - used) = p.c.bytes.drop used)
    (post : (Proof.Ffdh.sievedParameterCandidateContract abi 184).post (callState p used s)
      (t.withRegions (callRd p used s.sp) (callWr p))) : CandidatePost p used t := by
  have a0 := call_stackArg (j := 0) facts.argsFits memory (by decide)
  have a1 := call_stackArg (j := 1) facts.argsFits memory (by decide)
  have a2 := call_stackArg (j := 2) facts.argsFits memory (by decide)
  simp only [callValue] at a0 a1 a2
  have widthNat : (BitVec.ofNat 32 p.c.length).toNat = p.c.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.width_bounds; omega)]
  have bitsNat : (BitVec.ofNat 32 p.c.bits).toNat = p.c.bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.maxBits; omega)]
  have genNat : (BitVec.ofNat 32 p.c.generator).toNat = p.c.generator := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases p.c.generatorAllowed with eq | eq <;> omega)]
  have tapeNat : (BitVec.ofNat 32 (p.c.bytes.length - used)).toNat = p.c.bytes.length - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.tapeCount; omega)]
  sig_post [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at post
  rw [BitVec.setWidth_append_eq_right] at post
  simp only [args.out, args.width, args.usedPtr, args.bits, a0, a1, a2,
    widthNat, bitsNat, genNat, tapeNat] at post
  simp only [State.addr] at bytes
  rw [bytes] at post
  exact ⟨post.1, post.2.1, post.2.2⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
