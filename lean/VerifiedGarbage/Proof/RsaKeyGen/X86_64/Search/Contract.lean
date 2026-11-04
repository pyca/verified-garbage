module
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.RsaKeyGen.Generation
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.TCB.X86_64.Target

/-! # The RSA prime search's contract in terms of the machine

`vg_rsa_prime_search(out, out_len, used, e, e_len, p | p_len, rand, rand_len,
scratch, scratch_len, state)`: six arguments in registers and six on the
stack. The search uses 336 octets of stack: its frame of 160, its call's
frame of 40, the call's return address and the candidate's own 128.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search


open VG VG.X86_64
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit primeLenValid PrimeSearchResult)

/-- The stack the search uses below its return address. -/
abbrev stackUse : Nat := 336

def inOut (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .rdx, 8⟩
def inE (s : State) : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
def inP (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
def inRand (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
def inState (s : State) : Region := ⟨stackArg s 5, 32⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 48⟩

/-- The buffers the search writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inE s, inP s, inRand s, inArgs s]

/-- The width, the exponent, the other prime and the random octets on entry. -/
abbrev searchLen (s : State) : Nat := (s.gpr .rsi).toNat
abbrev searchE (s : State) : List Byte := bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
abbrev searchP (s : State) : List Byte := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
abbrev searchRand (s : State) : List Byte := bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
abbrev searchRemaining (s : State) : Nat := (s.mem.readW (stackArg s 5) 64).toNat

def searchPre (s : State) : Prop :=
  (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64 ∧ stackUse ≤ (s.gpr .rsp).toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧
      (below (s.gpr .rsp) stackUse).Disjoint r) ∧
    primeLenValid (searchLen s) ∧ 1 ≤ (s.gpr .r8).toNat ∧ (s.gpr .r8).toNat ≤ 8 ∧
    ((stackArg s 0).toNat = 0 ∨ (stackArg s 0).toNat = searchLen s) ∧
    Spec.Rsa.scratchWords (searchLen s) ≤ (stackArg s 4).toNat ∧
    searchRemaining s ≤ primeLimit (8 * searchLen s) (Spec.Rsa.os2ip (searchE s)) ∧
    s.mem.readW (stackArg s 5 + 8) 64 = BitVec.ofNat 64 (searchLen s) ∧
    s.mem.readW (stackArg s 5 + 16) 64 = BitVec.ofNat 64 (primeEntropy (searchLen s)) ∧
    (stackArg s 2).toNat ≤ primeEntropy (searchLen s)

def searchResult (s : State) : PrimeSearchResult :=
  primeSearch (searchLen s) (searchE s) (searchP s) (searchRemaining s) (searchRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .rdi) (searchLen s) =
      (match (searchResult s).outcome with
        | .accepted c => i2osp c (searchLen s)
        | _ => List.replicate (searchLen s) 0) ∧
    wordsAt t.mem (s.gpr .rdx) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    wordsAt t.mem (stackArg s 5) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (searchLen s), BitVec.ofNat 64 (primeEntropy (searchLen s)),
      BitVec.ofNat 64 (searchResult s).requested]

/-- What timing may depend on: the arguments but the octets of `p` and the
tape, `e`, the state's public words, and the result's status, consumption,
request and trace. -/
def searchPub (s t : State) : Prop :=
  s.gpr .rsp = t.gpr .rsp ∧
    s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧
    (∀ j < 6, stackArg s j = stackArg t j) ∧
    searchE s = searchE t ∧ wordsAt s.mem (stackArg s 5) 4 = wordsAt t.mem (stackArg t 5) 4 ∧
    (searchResult s).status = (searchResult t).status ∧ (searchResult s).used = (searchResult t).used ∧
    (searchResult s).requested = (searchResult t).requested ∧
    (searchResult s).trace = (searchResult t).trace

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.RsaKeyGen.X86_64.Search
