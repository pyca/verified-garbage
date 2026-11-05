module

public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.Arm.Target

/-! # The RSA prime search's contract in terms of the machine (ARMv7)

`vg_rsa_prime_search(out = r0, out_len = r1, used = r2, e = r3, e_len, p,
p_len, rand, rand_len, scratch, scratch_len, state)`: four arguments in
registers and eight on the stack. The search uses 184 bytes of stack: the
frame of 40 bytes saving the callee-saved registers, the candidate's frame of
32 bytes and the candidate's own 112 (`Cand.stack`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit primeLenValid PrimeSearchResult)

/-- The stack the search uses below the stack pointer. -/
abbrev stackUse : Nat := 184

/-- An implementation of `vg_rsa_keygen_candidate`, as the search calls it:
its name, its code, the stack it uses and its proof. -/
structure Cand where
  name : String
  code : Prog isa
  verified : Verified target code (Spec.RsaKeyGen.candidateContract abi 112)
  stack : FrameStack.armStack code ≤ 112

/-- The candidate, as the search calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
def inUsed (s : State) : Region := ⟨State.addr (s.gpr .r2), 8⟩
def inE (s : State) : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
def inP (s : State) : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
def inRand (s : State) : Region := ⟨State.addr (stackArg s 3), (stackArg s 4).toNat⟩
def inScr (s : State) : Region := ⟨State.addr (stackArg s 5), (stackArg s 6).toNat * 8⟩
def inState (s : State) : Region := ⟨State.addr (stackArg s 7), 32⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 32⟩

/-- The buffers the search writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inE s, inP s, inRand s, inArgs s]

/-- The stack below the stack pointer the search uses. -/
def inStack (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 stackUse, stackUse⟩

/-- The width, the exponent, the other prime and the random octets on entry. -/
abbrev searchLen (s : State) : Nat := (s.gpr .r1).toNat
abbrev searchE (s : State) : List Byte := bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
abbrev searchP (s : State) : List Byte := bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
abbrev searchRand (s : State) : List Byte := bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat
abbrev searchRemaining (s : State) : Nat := (s.mem.readW (State.addr (stackArg s 7)) 64).toNat

def searchPre (s : State) : Prop :=
  stackUse ≤ s.sp.toNat ∧ s.sp.toNat + 32 ≤ 2 ^ 32 ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (inStack s).Disjoint r) ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 32 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 32 ∧
    (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 32 ∧ (stackArg s 7).toNat + 32 ≤ 2 ^ 32 ∧
    primeLenValid (searchLen s) ∧ 1 ≤ (stackArg s 0).toNat ∧ (stackArg s 0).toNat ≤ 8 ∧
    ((stackArg s 2).toNat = 0 ∨ (stackArg s 2).toNat = searchLen s) ∧
    Spec.Rsa.scratchWords (searchLen s) ≤ (stackArg s 6).toNat ∧
    searchRemaining s ≤ primeLimit (8 * searchLen s) (Spec.Rsa.os2ip (searchE s)) ∧
    s.mem.readW (State.addr (stackArg s 7) + 8) 64 = BitVec.ofNat 64 (searchLen s) ∧
    s.mem.readW (State.addr (stackArg s 7) + 16) 64 = BitVec.ofNat 64 (primeEntropy (searchLen s)) ∧
    (stackArg s 4).toNat ≤ primeEntropy (searchLen s)

def searchResult (s : State) : PrimeSearchResult :=
  primeSearch (searchLen s) (searchE s) (searchP s) (searchRemaining s) (searchRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (State.addr (s.gpr .r0)) (searchLen s) =
      (match (searchResult s).outcome with
        | .accepted c => i2osp c (searchLen s)
        | _ => List.replicate (searchLen s) 0) ∧
    wordsAt t.mem (State.addr (s.gpr .r2)) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    wordsAt t.mem (State.addr (stackArg s 7)) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (searchLen s), BitVec.ofNat 64 (primeEntropy (searchLen s)),
      BitVec.ofNat 64 (searchResult s).requested]

/-- What timing may depend on: the arguments but the octets of `p` and the
tape, `e`, the state's public words, and the result's status, consumption,
request and trace. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧
    s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧
    (∀ j < 8, stackArg s j = stackArg t j) ∧
    searchE s = searchE t ∧
    wordsAt s.mem (State.addr (stackArg s 7)) 4 = wordsAt t.mem (State.addr (stackArg t 7)) 4 ∧
    (searchResult s).status = (searchResult t).status ∧ (searchResult s).used = (searchResult t).used ∧
    (searchResult s).requested = (searchResult t).requested ∧
    (searchResult s).trace = (searchResult t).trace

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.RsaKeyGen.Arm.Search
