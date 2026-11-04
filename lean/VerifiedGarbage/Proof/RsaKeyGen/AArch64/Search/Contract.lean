module

public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.Generation

/-! # The RSA prime search's contract in terms of the machine (AArch64)

`vg_rsa_prime_search(out = x0, out_len = x1, used = x2, e = x3, e_len = x4,
p = x5, p_len = x6, rand = x7, rand_len, scratch, scratch_len, state)`:
eight arguments in registers and four on the stack. The search uses 208
bytes of stack: its frame of 160, the frame saving `x30` and its candidate's
frame of 32; the candidate it calls has no frames (`Cand.noFrames`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit primeLenValid PrimeSearchResult)
open VG.Proof.RsaKeyGen.AArch64 (candContract candPre candPub)

/-- The stack the search uses below the stack pointer. -/
abbrev stackUse : Nat := 208

/-- An implementation of `vg_rsa_keygen_candidate`, as the search calls it:
its name, its code, which has no frames, and its proofs. -/
structure Cand where
  name : String
  code : Prog isa
  noFrames : code.noFrames = true
  correct : ∀ s, candContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ candContract.post s s'
  ct : ConstantTime isa candPre candPub code

/-- The candidate, as the search calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .x2, 8⟩
def inE (s : State) : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
def inP (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
def inRand (s : State) : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
def inState (s : State) : Region := ⟨stackArg s 3, 32⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 32⟩

/-- The buffers the search writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inE s, inP s, inRand s, inArgs s]

/-- The width, the exponent, the other prime, the random octets and the
counted candidates left on entry. -/
abbrev searchLen (s : State) : Nat := (s.gpr .x1).toNat
abbrev searchE (s : State) : List Byte := bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
abbrev searchP (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
abbrev searchRand (s : State) : List Byte := bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat
abbrev searchRemaining (s : State) : Nat := (s.mem.readW (stackArg s 3) 64).toNat

def searchPre (s : State) : Prop :=
  s.sp.toNat + 32 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    primeLenValid (searchLen s) ∧ 1 ≤ (s.gpr .x4).toNat ∧ (s.gpr .x4).toNat ≤ 8 ∧
    ((s.gpr .x6).toNat = 0 ∨ (s.gpr .x6).toNat = searchLen s) ∧
    Spec.Rsa.scratchWords (searchLen s) ≤ (stackArg s 2).toNat ∧
    searchRemaining s ≤ primeLimit (8 * searchLen s) (Spec.Rsa.os2ip (searchE s)) ∧
    s.mem.readW (stackArg s 3 + 8) 64 = BitVec.ofNat 64 (searchLen s) ∧
    s.mem.readW (stackArg s 3 + 16) 64 = BitVec.ofNat 64 (primeEntropy (searchLen s)) ∧
    (stackArg s 0).toNat ≤ primeEntropy (searchLen s)

def searchResult (s : State) : PrimeSearchResult :=
  primeSearch (searchLen s) (searchE s) (searchP s) (searchRemaining s) (searchRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .x0) (searchLen s) =
      (match (searchResult s).outcome with
        | .accepted c => i2osp c (searchLen s)
        | _ => List.replicate (searchLen s) 0) ∧
    wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    wordsAt t.mem (stackArg s 3) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (searchLen s), BitVec.ofNat 64 (primeEntropy (searchLen s)),
      BitVec.ofNat 64 (searchResult s).requested]

/-- What timing may depend on: the arguments but the octets of `p` and the
tape, `e`, the state's public words, and the result's status, consumption,
request and trace. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧
    s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧ s.gpr .x7 = t.gpr .x7 ∧
    (∀ j < 4, stackArg s j = stackArg t j) ∧
    searchE s = searchE t ∧ wordsAt s.mem (stackArg s 3) 4 = wordsAt t.mem (stackArg t 3) 4 ∧
    (searchResult s).status = (searchResult t).status ∧ (searchResult s).used = (searchResult t).used ∧
    (searchResult s).requested = (searchResult t).requested ∧
    (searchResult s).trace = (searchResult t).trace

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.RsaKeyGen.AArch64.Search
