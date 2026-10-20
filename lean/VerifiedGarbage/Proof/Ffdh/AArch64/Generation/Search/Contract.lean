module

public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Contract
public import VerifiedGarbage.Spec.Ffdh.Generation

/-! # The parameter-search controller's contract in terms of the machine (AArch64)

`vg_ffdh_generate_parameters(out = x0, out_len = x1, used = x2, bits = x3,
generator = w4, rand = x5, rand_len = x6, scratch = x7, scratch_len, state)`:
eight arguments in registers and two on the stack. The controller uses 32
bytes of stack: the frame saving `x30` and its candidate's frame of 16
bytes; the candidate it calls has no frames (`Cand.noFrames`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Proof.Ffdh.AArch64.ParameterCandidate (pcContract pcPre pcPub)

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 32

/-- An implementation of `vg_ffdh_parameter_candidate`, as the controller
calls it: its name, its code, which has no frames, and its proofs. -/
structure Cand where
  name : String
  code : Prog isa
  noFrames : code.noFrames = true
  correct : ∀ s, pcContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pcContract.post s s'
  ct : ConstantTime isa pcPre pcPub code

/-- The candidate, as the controller calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .x2, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 1, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inRand s, inArgs s]

/-- The width, the bits, the generator, the tape and the attempts on entry. -/
abbrev genLen (s : State) : Nat := (s.gpr .x1).toNat
abbrev genBits (s : State) : Nat := (s.gpr .x3).toNat
abbrev genGen (s : State) : Nat := ((s.gpr .x4).setWidth 32).toNat
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
abbrev genAttempts (s : State) : Nat := (s.mem.readW (stackArg s 1) 64).toNat

def searchPre (s : State) : Prop :=
  s.sp.toNat + 16 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    512 ≤ genBits s ∧ genBits s ≤ 8192 ∧ genLen s = (genBits s + 7) / 8 ∧
    (genGen s = 2 ∨ genGen s = 5) ∧
    Spec.Rsa.scratchWords (genLen s) ≤ (stackArg s 0).toNat ∧
    genAttempts s ≤ parameterAttempts (genBits s) ∧
    s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 (genLen s) ∧
    s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (parameterEntropy (genBits s)) ∧
    (s.gpr .x6).toNat ≤ parameterEntropy (genBits s)

def searchResult (s : State) : ParameterSearchResult :=
  parameterSearch (genBits s) (genGen s) (genAttempts s) (genRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .x0) (genLen s) =
      (match searchResult s with
        | .accepted p _ => i2osp p (genLen s)
        | _ => List.replicate (genLen s) 0) ∧
    wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    wordsAt t.mem (stackArg s 1) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (parameterEntropy (genBits s)),
      BitVec.ofNat 64 (searchResult s).requested]

/-- What timing may depend on: the arguments, the tape and the controller's
public words. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (genRand s).map (·.toNat) = (genRand t).map (·.toNat) ∧
    wordsAt s.mem (stackArg s 1) 4 = wordsAt t.mem (stackArg t 1) 4 ∧
    s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    (s.gpr .x4).setWidth 32 = (t.gpr .x4).setWidth 32 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧
    s.gpr .x7 = t.gpr .x7 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.Ffdh.AArch64.Generation
