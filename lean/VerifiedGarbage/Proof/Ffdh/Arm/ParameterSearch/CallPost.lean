module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.Arm.ParameterSearch.CallFacts`, which this module and modules that import it used -/

section

/-! The shared candidate contract's stack and incoming-argument separation facts. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

structure CallFacts (p : SearchParams) (used : Nat) (sp : BitVec 32) : Prop where
  stackFits : 184 ≤ sp.toNat
  argsFits : sp.toNat + 20 ≤ 2 ^ 32
  outputArgs : (⟨State.addr p.c.out, p.c.length⟩ : Region).Disjoint ⟨State.addr sp, 20⟩
  usedArgs : (⟨State.addr (p.control + 112#32), 8⟩ : Region).Disjoint ⟨State.addr sp, 20⟩
  scratchArgs : (⟨State.addr p.c.base, 8 * p.c.capacity⟩ : Region).Disjoint ⟨State.addr sp, 20⟩
  stackOutput : (FrameStack.belowA sp 184).Disjoint ⟨State.addr p.c.out, p.c.length⟩
  stackUsed : (FrameStack.belowA sp 184).Disjoint ⟨State.addr (p.control + 112#32), 8⟩
  stackTape : (FrameStack.belowA sp 184).Disjoint
    ⟨State.addr (p.c.tape + BitVec.ofNat 32 used), p.c.bytes.length - used⟩
  stackScratch : (FrameStack.belowA sp 184).Disjoint ⟨State.addr p.c.base, 8 * p.c.capacity⟩
  stackArgs : (FrameStack.belowA sp 184).Disjoint ⟨State.addr sp, 20⟩

theorem SearchBuffers.callFacts {p : SearchParams} {s : State} (h : SearchBuffers p s) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) : CallFacts p used (s.sp - 24#32) := by
  have argsSub : (⟨State.addr (s.sp - 24#32), 20⟩ : Region).Sub (FrameStack.belowA s.sp 208) :=
    fun a ha => callArguments_sub h.below a (Region.sub_prefix (by decide : 20 ≤ 24) a ha)
  have stackSub := callStack_sub h.below
  have out := (h.stackSeparate ⟨State.addr p.c.out, p.c.length⟩ (by simp)).2
  have control := (h.stackSeparate ⟨State.addr p.control, 128⟩ (by simp)).2
  have scratch := (h.stackSeparate ⟨State.addr p.c.base, 8 * p.c.capacity⟩ (by simp)).2
  have tape := (h.stackSeparate ⟨State.addr p.c.tape, p.c.bytes.length⟩ (by simp)).2
  exact ⟨callStack_fits h.below, by have := callArguments_fits h.below; omega_using [this],
    (out.sub_left argsSub).symm, ((control.sub_left argsSub).sub_right p.used_sub).symm,
    (scratch.sub_left argsSub).symm, out.sub_left stackSub,
    (control.sub_left stackSub).sub_right p.used_sub,
    (tape.sub_left stackSub).sub_right (p.source_sub used room), scratch.sub_left stackSub,
    callStack_arguments_separate h.below⟩

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.ArgumentWords`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterSearch.CallLayout`, which this module and modules that import it used -/

section

/-! The candidate receives only its output, private consumption word, scratch and entropy suffix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

def callRd (p : SearchParams) (used : Nat) (sp : BitVec 32) : List Region :=
  [⟨State.addr (p.c.tape + BitVec.ofNat 32 used), p.c.bytes.length - used⟩, ⟨State.addr sp, 20⟩]

def callWr (p : SearchParams) : List Region :=
  [⟨State.addr p.c.out, p.c.length⟩, ⟨State.addr (p.control + 112#32), 8⟩,
    ⟨State.addr p.c.base, 8 * p.c.capacity⟩]

abbrev callState (p : SearchParams) (used : Nat) (s : State) : State :=
  s.callEntry.withRegions (callRd p used s.sp) (callWr p)

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! Read the candidate's AAPCS arguments using the shared native stack-word lemmas. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

def callValue (p : SearchParams) (used : Nat) : Nat → BitVec 32
  | 0 => BitVec.ofNat 32 p.c.generator
  | 1 => p.c.tape + BitVec.ofNat 32 used
  | 2 => BitVec.ofNat 32 (p.c.bytes.length - used)
  | 3 => p.c.base
  | 4 => BitVec.ofNat 32 p.c.capacity
  | _ => 0

theorem callMem_word (p : SearchParams) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat} (bound : j < 5) :
    (callMem p used m sp).readW (off (State.addr sp) (4 * j)) 32 = callValue p used j := by
  change VG.Proof.Ffdh.Arm.KeySearch.stackWord (callMem p used m sp) sp j = _
  unfold callMem
  rw [VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 4) _ _ _ (by decide) (by omega_using [bound]),
    VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 3) _ _ _ (by decide) (by omega_using [bound]),
    VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 2) _ _ _ (by decide) (by omega_using [bound]),
    VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 1) _ _ _ (by decide) (by omega_using [bound]),
    VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 0) _ _ _ (by decide) (by omega_using [bound])]
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [bound]
  rcases casesJ with rfl | rfl | rfl | rfl | rfl <;> simp [callValue]

theorem call_stackArg {p : SearchParams} {used : Nat} {s : State} {m : Mem} {j : Nat}
    (fit : s.sp.toNat + 20 ≤ 2 ^ 32) (memory : s.mem = callMem p used m s.sp) (bound : j < 5) :
    stackArg (callState p used s) j = callValue p used j := by
  change s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * j))) 32 = _
  rw [VG.Arm.addr_add (by omega_using [fit, bound]), memory]
  exact callMem_word _ _ _ _ bound

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

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
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.width_bounds; omega_using [this])]
  have bitsNat : (BitVec.ofNat 32 p.c.bits).toNat = p.c.bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.maxBits; omega_using [this])]
  have genNat : (BitVec.ofNat 32 p.c.generator).toNat = p.c.generator := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases p.c.generatorAllowed with eq | eq <;> omega_using [eq])]
  have tapeNat : (BitVec.ofNat 32 (p.c.bytes.length - used)).toNat = p.c.bytes.length - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.tapeCount; omega_using [this])]
  sig_post [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at post
  rw [BitVec.setWidth_append_eq_right] at post
  simp only [args.out, args.width, args.usedPtr, args.bits, a0, a1, a2,
    widthNat, bitsNat, genNat, tapeNat] at post
  simp only [State.addr] at bytes
  rw [bytes] at post
  exact ⟨post.1, post.2.1, post.2.2⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
