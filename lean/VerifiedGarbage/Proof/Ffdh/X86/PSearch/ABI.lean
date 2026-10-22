module

public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI

/-! # The parameter search on i686: what its cdecl contract supplies

`vg_ffdh_generate_parameters_sieved(out, out_len, used, bits, generator, rand, rand_len, scratch,
scratch_len, state)`: ten arguments on the stack, and RSA's table of primes as a constant. The
controller uses 156 bytes of stack: its attempt's frame of 36, the call's return address and the
candidate's own 116.
-/

@[expose] public section
namespace VG.Proof.Ffdh.X86.PSearch
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The bytes of stack the controller uses. -/
abbrev stack : Nat := 156

/-- The contract, with RSA's table of primes as the constants. -/
abbrev contract : Contract isa :=
  Spec.Ffdh.sievedParameterSearchContract (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) stack

/-- The arguments' regions: `out`, `used`, `rand`, `scratch` and `state`. -/
abbrev oR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩
abbrev uR (s : State) : Region := ⟨argumentPointer s 2, 8⟩
abbrev rR (s : State) : Region := ⟨argumentPointer s 5, (arg s 6).toNat⟩
abbrev bR (s : State) : Region := ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
abbrev sR (s : State) : Region := ⟨argumentPointer s 9, 128⟩
/-- The arguments themselves. -/
abbrev aR (s : State) : Region := ⟨argAddr s 0, 40⟩
/-- The return address and the stack below it. -/
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 156#64, 156⟩
/-- RSA's table. -/
abbrev tR (s : State) : Region := ⟨(s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩

structure PSearchABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 40 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = Abi.constRegions (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]
  held : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64)
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)],
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧ t.Disjoint (retR s) ∧ t.Disjoint (lowR s)
  rdPrefix : s.rd.take (s.rd.length - 1) = [rR s]
  wr : s.wr = [oR s, uR s, bR s, sR s, aR s]
  ou : (oR s).Disjoint (uR s)
  or_ : (oR s).Disjoint (rR s)
  ob : (oR s).Disjoint (bR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR s)
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
  retO : (retR s).Disjoint (oR s)
  retU : (retR s).Disjoint (uR s)
  retRand : (retR s).Disjoint (rR s)
  retB : (retR s).Disjoint (bR s)
  retS : (retR s).Disjoint (sR s)
  retA : (retR s).Disjoint (aR s)
  lowO : (lowR s).Disjoint (oR s)
  lowU : (lowR s).Disjoint (uR s)
  lowRand : (lowR s).Disjoint (rR s)
  lowB : (lowR s).Disjoint (bR s)
  lowS : (lowR s).Disjoint (sR s)
  lowA : (lowR s).Disjoint (aR s)
  oBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  uBound : (arg s 2).toNat + 8 ≤ 2 ^ 32
  rBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  bBound : (arg s 7).toNat + (arg s 8).toNat * 8 ≤ 2 ^ 32
  sBound : (arg s 9).toNat + 128 ≤ 2 ^ 32
  bitsLow : 512 ≤ (arg s 3).toNat
  bitsHigh : (arg s 3).toNat ≤ 8192
  outLen : (arg s 1).toNat = ((arg s 3).toNat + 7) / 8
  gen : (arg s 4).toNat = 2 ∨ (arg s 4).toNat = 5
  scratchLength : Spec.Rsa.scratchWords (arg s 1).toNat ≤ (arg s 8).toNat
  attempts : (s.mem.readW (argumentPointer s 9) 64).toNat ≤ Spec.Ffdh.parameterAttempts (arg s 3).toNat
  width : s.mem.readW (argumentPointer s 9 + 8) 64 = BitVec.ofNat 64 (arg s 1).toNat
  cap : s.mem.readW (argumentPointer s 9 + 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy (arg s 3).toNat)
  randLen : (arg s 6).toNat ≤ Spec.Ffdh.parameterEntropy (arg s 3).toNat

theorem pSearchABI_of {s : State} (h : contract.pre s) : PSearchABI s := by
  sig_pre [contract, Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, VG.Proof.RsaKeyGen.X86.Candidate.packed_length,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Ffdh.X86.PSearch
