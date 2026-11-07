module

public import VerifiedGarbage.Proof.RsaKeyGen.SearchContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
meta import VerifiedGarbage.Proof.RsaKeyGen.SearchContract

/-! # The RSA prime search on i686: what its cdecl contract supplies

`vg_rsa_prime_search(out, out_len, used, e, e_len, p, p_len, rand,
rand_len, scratch, scratch_len, state)`: twelve arguments on the stack, and
RSA's table of primes as a constant (the candidate's).
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Search
open VG VG.X86

/-- The bytes of stack the search uses: its frame of 16 saving the callee-saved
registers, the candidate's frame of 44, the call's return address and the
candidate's own 152. -/
abbrev stack : Nat := 216

/-- The contract, with RSA's table of primes as the constants. -/
abbrev contract : Contract isa :=
  Proof.RsaKeyGen.primeSearchContract (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) stack

/-- The arguments' regions: `out`, `used`, `e`, `p`, `rand`, `scratch` and `state`. -/
abbrev oR (s : State) : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
abbrev uR (s : State) : Region := ⟨(arg s 2).setWidth 64, 8⟩
abbrev eR (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev pR (s : State) : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
abbrev rR (s : State) : Region := ⟨(arg s 7).setWidth 64, (arg s 8).toNat⟩
abbrev bR (s : State) : Region := ⟨(arg s 9).setWidth 64, (arg s 10).toNat * 8⟩
abbrev sR (s : State) : Region := ⟨(arg s 11).setWidth 64, 32⟩
/-- The arguments themselves. -/
abbrev aR (s : State) : Region := ⟨argAddr s 0, 48⟩
/-- The return address and the stack below it. -/
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 216#64, 216⟩
/-- RSA's table. -/
abbrev tableRegions (s : State) : List Region :=
  Abi.constRegions (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]

/-- The width, the exponent, the other prime, the tape and the counted
candidates left on entry. -/
abbrev searchLen (s : State) : Nat := (arg s 1).toNat
abbrev searchE (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (eR s).base (arg s 4).toNat
abbrev searchP (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (pR s).base (arg s 6).toNat
abbrev searchRand (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (rR s).base (arg s 8).toNat
abbrev searchRemaining (s : State) : Nat := (s.mem.readW (sR s).base 64).toNat

/-- The search the contract specifies. -/
def searchResult (s : State) : Spec.RsaKeyGen.PrimeSearchResult :=
  Spec.RsaKeyGen.primeSearch (searchLen s) (searchE s) (searchP s) (searchRemaining s) (searchRand s)

structure SearchABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 48 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = tableRegions s
  held : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]
  tableFar : ∀ t ∈ tableRegions s,
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧ t.Disjoint (retR s) ∧ t.Disjoint (lowR s)
  tableAligned : ∀ t ∈ tableRegions s, t.base.toNat % 64 = 0
  rdPrefix : s.rd.take (s.rd.length - 1) = [eR s, pR s, rR s]
  wr : s.wr = [oR s, uR s, bR s, sR s, aR s]
  ou : (oR s).Disjoint (uR s)
  oe : (oR s).Disjoint (eR s)
  op : (oR s).Disjoint (pR s)
  or_ : (oR s).Disjoint (rR s)
  ob : (oR s).Disjoint (bR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR s)
  ue : (uR s).Disjoint (eR s)
  up : (uR s).Disjoint (pR s)
  ur : (uR s).Disjoint (rR s)
  ub : (uR s).Disjoint (bR s)
  us : (uR s).Disjoint (sR s)
  ua : (uR s).Disjoint (aR s)
  eb : (eR s).Disjoint (bR s)
  es : (eR s).Disjoint (sR s)
  ea : (eR s).Disjoint (aR s)
  pb : (pR s).Disjoint (bR s)
  ps : (pR s).Disjoint (sR s)
  pa : (pR s).Disjoint (aR s)
  rb : (rR s).Disjoint (bR s)
  rs : (rR s).Disjoint (sR s)
  ra : (rR s).Disjoint (aR s)
  bs : (bR s).Disjoint (sR s)
  ba : (bR s).Disjoint (aR s)
  sa : (sR s).Disjoint (aR s)
  retO : (retR s).Disjoint (oR s)
  retU : (retR s).Disjoint (uR s)
  retE : (retR s).Disjoint (eR s)
  retP : (retR s).Disjoint (pR s)
  retRand : (retR s).Disjoint (rR s)
  retB : (retR s).Disjoint (bR s)
  retS : (retR s).Disjoint (sR s)
  retA : (retR s).Disjoint (aR s)
  lowO : (lowR s).Disjoint (oR s)
  lowU : (lowR s).Disjoint (uR s)
  lowE : (lowR s).Disjoint (eR s)
  lowP : (lowR s).Disjoint (pR s)
  lowRand : (lowR s).Disjoint (rR s)
  lowB : (lowR s).Disjoint (bR s)
  lowS : (lowR s).Disjoint (sR s)
  lowA : (lowR s).Disjoint (aR s)
  oBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  uBound : (arg s 2).toNat + 8 ≤ 2 ^ 32
  eBound : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  pBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  rBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  bBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  sBound : (arg s 11).toNat + 32 ≤ 2 ^ 32
  lenValid : Spec.RsaKeyGen.primeLenValid (arg s 1).toNat
  eLow : 1 ≤ (arg s 4).toNat
  eHigh : (arg s 4).toNat ≤ 8
  pLen : (arg s 6).toNat = 0 ∨ (arg s 6).toNat = (arg s 1).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 1).toNat ≤ (arg s 10).toNat
  remaining : searchRemaining s ≤ Spec.RsaKeyGen.primeLimit (8 * (arg s 1).toNat) (Spec.Rsa.os2ip (searchE s))
  width : s.mem.readW ((sR s).base + 8) 64 = BitVec.ofNat 64 (arg s 1).toNat
  budget : s.mem.readW ((sR s).base + 16) 64 = BitVec.ofNat 64 (Spec.RsaKeyGen.primeEntropy (arg s 1).toNat)
  randLen : (arg s 8).toNat ≤ Spec.RsaKeyGen.primeEntropy (arg s 1).toNat

theorem searchABI_of {s : State} (h : contract.pre s) : SearchABI s := by
  sig_pre [contract, Proof.RsaKeyGen.primeSearchContract, Proof.RsaKeyGen.primeSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, VG.Proof.RsaKeyGen.X86.Candidate.packed_length,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.RsaKeyGen.X86.Search
