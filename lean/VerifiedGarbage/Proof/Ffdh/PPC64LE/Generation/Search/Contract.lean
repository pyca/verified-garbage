module

public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Contract
public import VerifiedGarbage.Spec.Ffdh.Generation

/-! # The parameter-search controller's contract in terms of the machine (PPC64LE)

`vg_ffdh_generate_parameters(out = r3, out_len = r4, used = r5, bits = r6,
generator = r7, rand = r8, rand_len = r9, scratch = r10, scratch_len, state)`:
eight arguments in registers and two on the stack. The controller uses 336
bytes of stack: the frame of 48 bytes saving the link register, its
candidate's frame of 112 bytes, and the 176 bytes the candidate may use
below its own (`Cand.stack`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (pcContract pcPre pcPub)

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 336

/-- An implementation of `vg_ffdh_parameter_candidate`, as the controller
calls it: its name, its code, the stack it uses, and its proofs. -/
structure Cand where
  name : String
  code : Prog isa
  stack : sdepth code ≤ 176
  correct : ∀ s, pcContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pcContract.post s s'
  ct : ConstantTime isa pcPre pcPub code

/-- The candidate, as the controller calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .r5, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 1, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inRand s, inArgs s]

/-- The width, the bits, the generator, the tape and the attempts on entry. -/
abbrev genLen (s : State) : Nat := (s.gpr .r4).toNat
abbrev genBits (s : State) : Nat := (s.gpr .r6).toNat
abbrev genGen (s : State) : Nat := ((s.gpr .r7).setWidth 32).toNat
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
abbrev genAttempts (s : State) : Nat := (s.mem.readW (stackArg s 1) 64).toNat

def searchPre (s : State) : Prop :=
  s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
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
    (s.gpr .r9).toNat ≤ parameterEntropy (genBits s)

def searchResult (s : State) : ParameterSearchResult :=
  parameterSearch (genBits s) (genGen s) (genAttempts s) (genRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .r3) (genLen s) =
      (match searchResult s with
        | .accepted p _ => i2osp p (genLen s)
        | _ => List.replicate (genLen s) 0) ∧
    wordsAt t.mem (s.gpr .r5) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    wordsAt t.mem (stackArg s 1) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (parameterEntropy (genBits s)),
      BitVec.ofNat 64 (searchResult s).requested]

/-- What timing may depend on: the arguments, the tape and the controller's
public words. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (genRand s).map (·.toNat) = (genRand t).map (·.toNat) ∧
    wordsAt s.mem (stackArg s 1) 4 = wordsAt t.mem (stackArg t 1) 4 ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧
    (s.gpr .r7).setWidth 32 = (t.gpr .r7).setWidth 32 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧
    s.gpr .r10 = t.gpr .r10 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.Ffdh.PPC64LE.Generation
