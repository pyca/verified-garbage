module

public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
meta import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract

/-! # RSA key generation on i686: what its cdecl contract supplies -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Generate
open VG VG.X86

abbrev stack : Nat := 284

abbrev contract : Contract isa :=
  Spec.RsaKeyGen.keySearchContract (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) stack

/-- The arguments' regions: `key`, `used`, `rand`, `scratch`, `state` and the arguments. -/
abbrev kR (s : State) : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
abbrev uR (s : State) : Region := ⟨(arg s 2).setWidth 64, 8⟩
abbrev rR (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev bR (s : State) : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
abbrev sR (s : State) : Region := ⟨(arg s 7).setWidth 64, 56⟩
abbrev aR (s : State) : Region := ⟨argAddr s 0, 32⟩
/-- The return address and the stack below it. -/
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 284#64, 284⟩
/-- RSA's table. -/
abbrev tableRegions (s : State) : List Region :=
  Abi.constRegions (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]

/-- The state's words: the primes' octets, and the state at `state`. -/
abbrev genLen (s : State) : Nat := (s.mem.readW ((arg s 7).setWidth 64 + 8) 64).toNat
abbrev genE (s : State) : List Byte := Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64 + 48) 8
abbrev genRand (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (rR s).base (arg s 4).toNat

structure GenABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 32 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = tableRegions s
  held : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]
  tableFar : ∀ t ∈ tableRegions s,
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧ t.Disjoint (retR s) ∧ t.Disjoint (lowR s)
  tableAligned : ∀ t ∈ tableRegions s, t.base.toNat % 64 = 0
  rdPrefix : s.rd.take (s.rd.length - 1) = [rR s]
  wr : s.wr = [kR s, uR s, bR s, sR s, aR s]
  ku : (kR s).Disjoint (uR s)
  kr : (kR s).Disjoint (rR s)
  kb : (kR s).Disjoint (bR s)
  ks : (kR s).Disjoint (sR s)
  ka : (kR s).Disjoint (aR s)
  ur : (uR s).Disjoint (rR s)
  ub : (uR s).Disjoint (bR s)
  us : (uR s).Disjoint (sR s)
  ua : (uR s).Disjoint (aR s)
  rb : (rR s).Disjoint (bR s)
  rs : (rR s).Disjoint (sR s)
  ra : (rR s).Disjoint (aR s)
  bs : (bR s).Disjoint (sR s)
  ba : (bR s).Disjoint (aR s)
  sa : (sR s).Disjoint (aR s)
  retK : (retR s).Disjoint (kR s)
  retU : (retR s).Disjoint (uR s)
  retRand : (retR s).Disjoint (rR s)
  retB : (retR s).Disjoint (bR s)
  retS : (retR s).Disjoint (sR s)
  retA : (retR s).Disjoint (aR s)
  lowK : (lowR s).Disjoint (kR s)
  lowU : (lowR s).Disjoint (uR s)
  lowRand : (lowR s).Disjoint (rR s)
  lowB : (lowR s).Disjoint (bR s)
  lowS : (lowR s).Disjoint (sR s)
  lowA : (lowR s).Disjoint (aR s)
  kBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  uBound : (arg s 2).toNat + 8 ≤ 2 ^ 32
  rBound : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  bBound : (arg s 5).toNat + (arg s 6).toNat * 8 ≤ 2 ^ 32
  sBound : (arg s 7).toNat + 56 ≤ 2 ^ 32
  lenValid : Spec.RsaKeyGen.primeLenValid (genLen s)
  keyLen : (arg s 1).toNat = 9 * genLen s
  scratchLength : Spec.Rsa.scratchWords (2 * genLen s) ≤ (arg s 6).toNat
  remaining : (s.mem.readW ((arg s 7).setWidth 64) 64).toNat ≤
    Spec.RsaKeyGen.primeLimit (8 * genLen s) (Spec.Rsa.os2ip (genE s))
  budget : s.mem.readW ((arg s 7).setWidth 64 + 16) 64 = BitVec.ofNat 64 (Spec.RsaKeyGen.primeEntropy (genLen s))
  phase : (s.mem.readW ((arg s 7).setWidth 64 + 32) 64).toNat ≤ 1
  randLen : (arg s 4).toNat ≤ Spec.RsaKeyGen.primeEntropy (genLen s)

theorem genABI_of {s : State} (h : contract.pre s) : GenABI s := by
  sig_pre [contract, Spec.RsaKeyGen.keySearchContract, Spec.RsaKeyGen.keySearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, VG.Proof.RsaKeyGen.X86.Candidate.packed_length,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.RsaKeyGen.X86.Generate
