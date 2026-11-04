module

public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTBase
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Fin
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Tail
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.Generation

/-! # The RSA prime search's contract in terms of the machine (PPC64LE)

`vg_rsa_prime_search(out = r3, out_len = r4, used = r5, e = r6, e_len = r7,
p = r8, p_len = r9, rand = r10, rand_len, scratch, scratch_len, state)`:
eight arguments in registers and four on the stack. The search uses 768
bytes of stack: its frame of 192, the frame of 48 saving the link register,
its candidate's frame of 128 bytes, and the 400 bytes the candidate may use
below its own (`Cand.stack`).

The candidate reads the table of trial division (`TrialTable32`), so the
search's contract is under `abi.withConsts`: its precondition is the one
under `abi` for the state without the table's region (`stripConsts`), with
what the table adds (`ConstsOk`), as `pre_consts` states it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Search

open VG VG.PPC64LE
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit primeLenValid PrimeSearchResult)
open VG.Proof.RsaKeyGen.PPC64LE.Cand (CIn TabOk CQ KRel)
open VG.Proof.Bignum.PPC64LE (Two)

/-- The stack the search uses below the stack pointer. -/
abbrev stackUse : Nat := 768

/-- The table of trial division. -/
abbrev tables : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

/-- An implementation of `vg_rsa_keygen_candidate`, as the search calls it:
its name, its code, the stack it uses, and its proofs, in the terms of the
candidate's own (`Proof/RsaKeyGen/PPC64LE/Cand/`). -/
structure Cand where
  name : String
  code : Prog isa
  stack : sdepth code ≤ 400
  correct : ∀ s, CIn s → TabOk s → WP isa code s fun t => abiPreserved s t ∧ CQ s (t.gpr .r3) t.mem
  ct : RelCT isa (Two KRel) code fun _ _ => True

/-- The candidate, as the search calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .r5, 8⟩
def inE (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
def inP (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
def inRand (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
def inState (s : State) : Region := ⟨stackArg s 3, 32⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 32⟩

/-- The buffers the search writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inE s, inP s, inRand s, inArgs s]

/-- The width, the exponent, the other prime and the random octets on entry. -/
abbrev searchLen (s : State) : Nat := (s.gpr .r4).toNat
abbrev searchE (s : State) : List Byte := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
abbrev searchP (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
abbrev searchRand (s : State) : List Byte := bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat
abbrev searchRemaining (s : State) : Nat := (s.mem.readW (stackArg s 3) 64).toNat

/-- The precondition without the table. -/
def basePre (s : State) : Prop :=
  s.sp.toNat + 32 + 8 * 12 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    primeLenValid (searchLen s) ∧ 1 ≤ (s.gpr .r7).toNat ∧ (s.gpr .r7).toNat ≤ 8 ∧
    ((s.gpr .r9).toNat = 0 ∨ (s.gpr .r9).toNat = searchLen s) ∧
    Spec.Rsa.scratchWords (searchLen s) ≤ (stackArg s 2).toNat ∧
    searchRemaining s ≤ primeLimit (8 * searchLen s) (Spec.Rsa.os2ip (searchE s)) ∧
    s.mem.readW (stackArg s 3 + 8) 64 = BitVec.ofNat 64 (searchLen s) ∧
    s.mem.readW (stackArg s 3 + 16) 64 = BitVec.ofNat 64 (primeEntropy (searchLen s)) ∧
    (stackArg s 0).toNat ≤ primeEntropy (searchLen s)

def searchPre (s : State) : Prop := basePre (stripConsts tables s) ∧ ConstsOk tables stackUse s

def searchResult (s : State) : PrimeSearchResult :=
  primeSearch (searchLen s) (searchE s) (searchP s) (searchRemaining s) (searchRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .r3) (searchLen s) =
      (match (searchResult s).outcome with
        | .accepted c => i2osp c (searchLen s)
        | _ => List.replicate (searchLen s) 0) ∧
    wordsAt t.mem (s.gpr .r5) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    wordsAt t.mem (stackArg s 3) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (searchLen s), BitVec.ofNat 64 (primeEntropy (searchLen s)),
      BitVec.ofNat 64 (searchResult s).requested]

/-- What timing may depend on: the arguments but the octets of `p` and the
tape, `e`, the state's public words, and the result's status, consumption,
request and trace; and the table's address. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧
    s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧ s.gpr .r10 = t.gpr .r10 ∧
    (∀ j < 4, stackArg s j = stackArg t j) ∧
    searchE s = searchE t ∧ wordsAt s.mem (stackArg s 3) 4 = wordsAt t.mem (stackArg t 3) 4 ∧
    (searchResult s).status = (searchResult t).status ∧ (searchResult s).used = (searchResult t).used ∧
    (searchResult s).requested = (searchResult t).requested ∧
    (searchResult s).trace = (searchResult t).trace ∧
    s.syms Impl.RsaKeyGen.TrialTable32.symbol = t.syms Impl.RsaKeyGen.TrialTable32.symbol

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.RsaKeyGen.PPC64LE.Search
