module

public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTTop
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Fin
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Main
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.Generation

/-! # The RSA prime search's contract in terms of the machine (RISCV64)

`vg_rsa_prime_search(out = a0, out_len = a1, used = a2, e = a3, e_len = a4,
p = a5, p_len = a6, rand = a7, rand_len, scratch, scratch_len, state)`:
eight arguments in registers and four on the stack. The search uses 496
bytes of stack: its frame of 160, the frame of 16 saving `ra`, its
candidate's frame of 32 bytes, and the 288 bytes the candidate may use below
its own (`Cand.stack`).

The candidate reads the table of trial division (`TrialTable32`), so the
search's contract is under `abi.withConsts`: its precondition is the one
under `abi` for the state without the table's region (`stripConsts`), with
what the table adds (`ConstsOk`), as `pre_consts` states it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Search

open VG VG.RISCV64
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit primeLenValid PrimeSearchResult)
open VG.Proof.RsaKeyGen.RISCV64.Cand (CIn TabOk CQ KR)
open VG.Proof.Bignum.RISCV64.Pre (Two)

/-- The stack the search uses below the stack pointer. -/
abbrev stackUse : Nat := 496

/-- The table of trial division. -/
abbrev tables : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

/-- An implementation of `vg_rsa_keygen_candidate`, as the search calls it:
its name, its code, the stack it uses, and its proofs, in the terms of the
candidate's own (`Proof/RsaKeyGen/RISCV64/Cand/`). -/
structure Cand where
  name : String
  code : Prog isa
  stack : sdepth code ≤ 288
  correct : ∀ s, CIn s → TabOk s → WP isa code s fun t => abiPreserved s t ∧ CQ s (t.gpr .a0) t.mem
  ct : RelCT isa (Two KR) code fun _ _ => True

/-- The candidate, as the search calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .a2, 8⟩
def inE (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
def inP (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
def inRand (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
def inState (s : State) : Region := ⟨stackArg s 3, 32⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 32⟩

/-- The buffers the search writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inE s, inP s, inRand s, inArgs s]

/-- The width, the exponent, the other prime and the random octets on entry. -/
abbrev searchLen (s : State) : Nat := (s.gpr .a1).toNat
abbrev searchE (s : State) : List Byte := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
abbrev searchP (s : State) : List Byte := bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat
abbrev searchRand (s : State) : List Byte := bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat
abbrev searchRemaining (s : State) : Nat := (s.mem.readW (stackArg s 3) 64).toNat

/-- The precondition without the table. -/
def basePre (s : State) : Prop :=
  s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 32 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    primeLenValid (searchLen s) ∧ 1 ≤ (s.gpr .a4).toNat ∧ (s.gpr .a4).toNat ≤ 8 ∧
    ((s.gpr .a6).toNat = 0 ∨ (s.gpr .a6).toNat = searchLen s) ∧
    Spec.Rsa.scratchWords (searchLen s) ≤ (stackArg s 2).toNat ∧
    searchRemaining s ≤ primeLimit (8 * searchLen s) (Spec.Rsa.os2ip (searchE s)) ∧
    s.mem.readW (stackArg s 3 + 8) 64 = BitVec.ofNat 64 (searchLen s) ∧
    s.mem.readW (stackArg s 3 + 16) 64 = BitVec.ofNat 64 (primeEntropy (searchLen s)) ∧
    (stackArg s 0).toNat ≤ primeEntropy (searchLen s) ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ (stackArg s 1).toNat % 8 = 0 ∧ (stackArg s 3).toNat % 8 = 0

def searchPre (s : State) : Prop := basePre (stripConsts tables s) ∧ ConstsOk tables stackUse s

def searchResult (s : State) : PrimeSearchResult :=
  primeSearch (searchLen s) (searchE s) (searchP s) (searchRemaining s) (searchRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .a0) (searchLen s) =
      (match (searchResult s).outcome with
        | .accepted c => i2osp c (searchLen s)
        | _ => List.replicate (searchLen s) 0) ∧
    wordsAt t.mem (s.gpr .a2) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    wordsAt t.mem (stackArg s 3) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (searchLen s), BitVec.ofNat 64 (primeEntropy (searchLen s)),
      BitVec.ofNat 64 (searchResult s).requested]

/-- What timing may depend on: the arguments but the octets of `p` and the
tape, `e`, the state's public words, and the result's status, consumption,
request and trace; and the table's address. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧
    s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧
    s.gpr .a4 = t.gpr .a4 ∧ s.gpr .a5 = t.gpr .a5 ∧ s.gpr .a6 = t.gpr .a6 ∧ s.gpr .a7 = t.gpr .a7 ∧
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

end VG.Proof.RsaKeyGen.RISCV64.Search
